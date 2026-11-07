import WebP.Decode
/-!
# File metadata without decoding

`WebP.info d` parses the container (`Container.demux`, the same proven parser the decoder
uses) and only the *headers* of the bitstreams: the VP8L header (§3.4) of lossless images and
the frame + first-partition headers of lossy images (RFC 6386 §9.1–§9.6, up to the token
partition table), never the pixel data.

It checks everything `WebP.decode` checks before decoding pixels: the container grammar, the
bitstream header checks, that a still image's bitstream size equals the VP8X canvas, and that
each animation frame's bitstream size equals its 'ANMF' size.

`WebP.Proofs.Info` proves that it agrees with decoding: if `WebP.decode d = .ok o` (equivalently
`Spec.Decodes Spec.lossy d o`), then `info d = .ok i` with the same canvas size, flags, loop
count, background color and frame durations (`info_of_decode`). The converse does not hold: a
file whose pixel data is corrupt can still have valid metadata.
-/
namespace WebP

open WebP.Spec

/-- Per-frame metadata. A still image is a single frame at `(0, 0)` with duration 0. -/
structure FrameMeta where
  /-- Offset of the frame on the canvas (`2 * Frame X`, `2 * Frame Y`, §2.7.1.1). -/
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  /-- Display duration in milliseconds. -/
  duration : Nat
  /-- Blending method: `true` = alpha-blend, `false` = do not blend. -/
  blend : Bool
  /-- Disposal method: `true` = dispose to the background color. -/
  dispose : Bool
  /-- 'VP8 ' bitstream (lossy); otherwise 'VP8L' (lossless). -/
  lossy : Bool
  /-- Lossy: an 'ALPH' chunk is present. Lossless: the `alpha_is_used` header hint (§3.4). -/
  hasAlpha : Bool
deriving Repr, DecidableEq, Inhabited

/-- File metadata. The fields shared with `Spec.Output` have the same meaning there. -/
structure Info where
  /-- Canvas size (the image size for still images). -/
  width : Nat
  height : Nat
  animated : Bool
  /-- VP8X alpha flag for extended files; the VP8L `alpha_is_used` hint for simple lossless
  files; `false` for simple lossy files. -/
  hasAlpha : Bool
  /-- Some image data is lossy ('VP8 '). -/
  lossy : Bool
  /-- Animation loop count (0 = infinite); 0 for still images. -/
  loopCount : Nat
  /-- Raw 'ANIM' background color (bytes B, G, R, A, little-endian); 0 for still images. -/
  background : Nat
  /-- The file has a 'VP8X' chunk (extended format, §2.7). -/
  extended : Bool
  /-- First 'ICCP', 'EXIF' and 'XMP ' chunks of an extended file (payload offset and size). -/
  iccp : Option Chunk
  exif : Option Chunk
  xmp : Option Chunk
  frames : List FrameMeta
deriving Repr

/-- Header of a bitstream chunk: width, height and the VP8L `alpha_is_used` hint (`false` for
'VP8 '). A 'VP8 ' payload is checked up to and including its first-partition headers. -/
def bitstreamHeader (d : ByteArray) (bits : Chunk) : Except String (Nat × Nat × Bool) :=
  if bits.tag = VP8L then VP8L.readHeaderOnly (Spec.payload d bits)
  else do
    let H ← Spec.VP8.decodeHeaders VP8.fastPrims (Spec.payload d bits)
    pure (H.hdr.w, H.hdr.h, false)

/-- Frame metadata of an animation, checking each bitstream's size against its 'ANMF' size. -/
def animFrames (d : ByteArray) : List FrameInfo → Except String (List FrameMeta)
  | [] => .ok []
  | f :: fs => do
    let (w, h, hint) ← bitstreamHeader d f.bits
    if w ≠ f.width ∨ h ≠ f.height then
      throw "frame bitstream size differs from ANMF size"
    let rest ← animFrames d fs
    let lossy := f.bits.tag == VP8
    return ⟨f.x, f.y, f.width, f.height, f.duration, f.blend, f.dispose, lossy,
      if lossy then f.alph.isSome else hint⟩ :: rest

/-- The metadata of frame `f` whose bitstream header gave the alpha hint `hint`. -/
def frameMeta (f : FrameInfo) (hint : Bool) : FrameMeta :=
  let lossy := f.bits.tag == VP8
  ⟨f.x, f.y, f.width, f.height, f.duration, f.blend, f.dispose, lossy,
    if lossy then f.alph.isSome else hint⟩

/-- `animFrames` with an accumulator; compiled code uses it (`@[csimp]`, proven equal) so that
long animations run in constant stack space. -/
def animFramesTR.go (d : ByteArray) : List FrameInfo → List FrameMeta → Except String (List FrameMeta)
  | [], acc => .ok acc.reverse
  | f :: fs, acc =>
    match bitstreamHeader d f.bits with
    | .error e => .error e
    | .ok (w, h, hint) =>
      if w ≠ f.width ∨ h ≠ f.height then .error "frame bitstream size differs from ANMF size"
      else go d fs (frameMeta f hint :: acc)

def animFramesTR (d : ByteArray) (fs : List FrameInfo) : Except String (List FrameMeta) :=
  animFramesTR.go d fs []

theorem animFramesTR_go (d : ByteArray) : ∀ (fs : List FrameInfo) (acc : List FrameMeta),
    animFramesTR.go d fs acc = (animFrames d fs).map (acc.reverse ++ ·)
  | [], acc => by simp [animFramesTR.go, animFrames, Except.map]
  | f :: fs, acc => by
    simp only [animFramesTR.go, animFrames, bind, Except.bind]
    cases bitstreamHeader d f.bits with
    | error e => simp [Except.map]
    | ok r =>
      obtain ⟨w, h, hint⟩ := r
      simp only []
      split
      · simp [Except.map, throw, throwThe, MonadExceptOf.throw]
      · rw [animFramesTR_go d fs]
        cases animFrames d fs <;> simp [Except.map, pure, Except.pure, frameMeta]

@[csimp] theorem animFrames_eq_animFramesTR : @animFrames = @animFramesTR := by
  funext d fs
  rw [animFramesTR, animFramesTR_go]
  cases animFrames d fs <;> simp [Except.map]

/-- Metadata of a demuxed file (mirrors `Spec.decodeLayout`). -/
def infoOfLayout (d : ByteArray) : Layout → Except String Info
  | .still vp8x alph bits => do
    let (w, h, hint) ← bitstreamHeader d bits
    let hasAlpha ← match vp8x with
      | none => pure hint
      | some x =>
        if w ≠ x.canvasWidth ∨ h ≠ x.canvasHeight then
          throw "bitstream size differs from canvas size"
        else pure x.alpha
    let lossy := bits.tag == VP8
    return ⟨w, h, false, hasAlpha, lossy, 0, 0, vp8x.isSome, none, none, none,
      [⟨0, 0, w, h, 0, false, false, lossy, if lossy then alph.isSome else hint⟩]⟩
  | .animated x bg loops frames => do
    let fs ← animFrames d frames
    return ⟨x.canvasWidth, x.canvasHeight, true, x.alpha, frames.any isLossyFrame, loops, bg,
      true, none, none, none, fs⟩

/-- First top-level chunk with the given FourCC. -/
def findChunk (cs : List Chunk) (tag : Nat) : Option Chunk := cs.find? (·.tag == tag)

/-- **File metadata**, without decoding pixel data. -/
def info (d : ByteArray) : Except String Info := do
  let L ← Container.demux d
  let i ← infoOfLayout d L
  if i.extended then
    -- §2.7.1.4/§2.7.1.5: only the first 'ICCP' is used; at most one 'EXIF'/'XMP ' SHOULD exist.
    let cs ← Container.parseRiff d
    return { i with iccp := findChunk cs ICCP, exif := findChunk cs EXIF, xmp := findChunk cs XMP }
  else return i

end WebP

import WebP.Spec.Anim
/-!
# Canvas assembly, in place

The specification (`Spec.Anim`) defines every canvas pointwise over all of its bytes. This
version touches only each frame's rectangle, updating the canvas in place, and creates the
initial zero canvas by doubling. `WebP.Proofs.Anim.compose_eq` proves
`WebP.Anim.compose = Spec.Anim.compose`.
-/
namespace WebP.Anim

open WebP.Spec WebP.Spec.Anim

/-- A zero-filled byte array of size `n`, built by doubling (no boxed intermediate array). -/
def zeros : Nat → ByteArray
  | 0 => .empty
  | n + 1 =>
    let h := zeros ((n + 1) / 2)
    let d := h ++ h
    if (n + 1) % 2 = 1 then d.push 0 else d
decreasing_by omega

/-- Overwrite the 4 bytes of pixel `p` with `g c t` (`c < 4`), where `t ch` are the pixel's
bytes before the update. They are read first, so `g` never sees a partly updated pixel. -/
@[inline] def writePx (g : Nat → (Nat → Nat) → UInt8) (cv : ByteArray) (p : Nat) :
    ByteArray :=
  let t0 := byte cv (4 * p)
  let t1 := byte cv (4 * p + 1)
  let t2 := byte cv (4 * p + 2)
  let t3 := byte cv (4 * p + 3)
  let t : Nat → Nat := fun ch => if ch = 0 then t0 else if ch = 1 then t1 else
    if ch = 2 then t2 else t3
  let v0 := g 0 t
  let v1 := g 1 t
  let v2 := g 2 t
  let v3 := g 3 t
  (((cv.set! (4 * p) v0).set! (4 * p + 1) v1).set! (4 * p + 2) v2).set! (4 * p + 3) v3

/-- Pixels `p, p+1, …, p+n-1`, with `g q c t` the new byte `c` of pixel `q`. -/
@[specialize] def rowLoop (g : Nat → Nat → (Nat → Nat) → UInt8) :
    ByteArray → Nat → Nat → ByteArray
  | cv, _, 0 => cv
  | cv, p, n + 1 => rowLoop g (writePx (g p) cv p) (p + 1) n

/-- Rows `y, …, y+n-1` of the rectangle with columns `x0, …, x0+wd-1` (canvas width `W`). -/
@[specialize] def rectLoop (g : Nat → Nat → (Nat → Nat) → UInt8) (W x0 wd : Nat) :
    ByteArray → Nat → Nat → ByteArray
  | cv, _, 0 => cv
  | cv, y, n + 1 => rectLoop g W x0 wd (rowLoop g cv (y * W + x0) wd) (y + 1) n

/-- Apply `g` to the pixels of frame `f`'s rectangle, clipped to the canvas width. -/
@[inline] def fillRect (g : Nat → Nat → (Nat → Nat) → UInt8) (W : Nat) (f : FrameInfo)
    (cv : ByteArray) : ByteArray :=
  rectLoop g W f.x (min (f.x + f.width) W - f.x) cv f.y f.height

/-- Byte `c` of canvas pixel `p` inside frame `f` after rendering, given the pixel's current
bytes `t` (the in-rectangle branch of `Spec.Anim.renderFrame`). -/
@[inline] def renderByte (W : Nat) (f : FrameInfo) (img : ByteArray) (p c : Nat)
    (t : Nat → Nat) : UInt8 :=
  let x := p % W
  let y := p / W
  let q := (y - f.y) * f.width + (x - f.x)
  let s := fun ch => byte img (4 * q + ch)
  if f.blend then
    (if c = 3 then blendAlpha (s 3) (t 3) else blendColor (s c) (s 3) (t c) (t 3)).toUInt8
  else (s c).toUInt8

/-- `Spec.Anim.renderFrame`, touching only the frame rectangle. -/
def renderFrame (W : Nat) (canvas : ByteArray) (f : FrameInfo) (img : ByteArray) : ByteArray :=
  if W = 0 then Spec.Anim.renderFrame W canvas f img
  else fillRect (renderByte W f img) W f canvas

/-- `Spec.Anim.disposeFrame`, touching only the frame rectangle. -/
def disposeFrame (W : Nat) (canvas : ByteArray) (f : FrameInfo) : ByteArray :=
  if W = 0 then Spec.Anim.disposeFrame W canvas f
  else fillRect (fun _ _ _ => 0) W f canvas

/-- **Canvas assembly** (`= Spec.Anim.compose`). -/
def compose (W H : Nat) (frames : List (FrameInfo × ByteArray)) : List ByteArray :=
  go (zeros (W * H * 4)) none frames []
where
  /-- Tail-recursive: `acc` holds the canvases so far, most recent first. -/
  go (canvas : ByteArray) (prev : Option FrameInfo) :
      List (FrameInfo × ByteArray) → List ByteArray → List ByteArray
    | [], acc => acc.reverse
    | (f, img) :: rest, acc =>
      let disposed := match prev with
        | some p => if p.dispose then disposeFrame W canvas p else canvas
        | none => canvas
      let shown := renderFrame W disposed f img
      go shown (some f) rest (shown :: acc)

end WebP.Anim

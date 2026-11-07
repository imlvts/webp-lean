import WebP.Spec.Container
/-!
# WebP demuxer

Executable parser for the container grammar `WebP.Spec.Demux`;
`WebP.Proofs.Container` proves `demux d = .ok L ↔ Spec.Demux d L`.

`parseChunks` and `parseFrames` recurse once per chunk/frame. Each has a tail-recursive twin
(`…TR`) proven equal to it and registered with `@[csimp]`, so compiled code uses the twin and
runs in constant stack space; proofs keep reasoning about the plain definitions.
-/
namespace WebP.Container

open WebP.Spec

/-- Parse the chunk sequence filling exactly `[p, stop)`. -/
def parseChunks (d : ByteArray) (p stop : Nat) : Except String (List Chunk) :=
  if p = stop then .ok []
  else if stop < p + 8 then .error "truncated chunk header"
  else
    let size := u32 d (p + 4)
    let next := p + 8 + size + size % 2
    if stop < next then .error "chunk exceeds its container"
    else
      match parseChunks d next stop with
      | .ok cs => .ok (⟨u32 d p, p + 8, size⟩ :: cs)
      | .error e => .error e
termination_by stop - p

/-- `parseChunks` with an accumulator (chunks in reverse order). -/
def parseChunksTR.go (d : ByteArray) (stop : Nat) (p : Nat) (acc : List Chunk) :
    Except String (List Chunk) :=
  if p = stop then .ok acc.reverse
  else if stop < p + 8 then .error "truncated chunk header"
  else
    let size := u32 d (p + 4)
    let next := p + 8 + size + size % 2
    if stop < next then .error "chunk exceeds its container"
    else go d stop next (⟨u32 d p, p + 8, size⟩ :: acc)
termination_by stop - p

def parseChunksTR (d : ByteArray) (p stop : Nat) : Except String (List Chunk) :=
  parseChunksTR.go d stop p []

theorem parseChunksTR_go_aux (d : ByteArray) (stop : Nat) : ∀ n p (acc : List Chunk),
    stop - p ≤ n →
    parseChunksTR.go d stop p acc = (parseChunks d p stop).map (acc.reverse ++ ·) := by
  intro n
  induction n with
  | zero =>
    intro p acc hn
    rw [parseChunksTR.go]
    conv => rhs; rw [parseChunks]
    by_cases h1 : p = stop
    · simp [h1, Except.map]
    · have h2 : stop < p + 8 := by omega
      simp [h1, h2, Except.map]
  | succ n ih =>
    intro p acc hn
    rw [parseChunksTR.go]
    conv => rhs; rw [parseChunks]
    by_cases h1 : p = stop
    · simp [h1, Except.map]
    by_cases h2 : stop < p + 8
    · simp [h1, h2, Except.map]
    by_cases h3 : stop < p + 8 + u32 d (p + 4) + u32 d (p + 4) % 2
    · simp [h1, h2, h3, Except.map]
    · simp only [h1, h2, h3, ite_false]
      rw [ih _ _ (by omega)]
      cases parseChunks d (p + 8 + u32 d (p + 4) + u32 d (p + 4) % 2) stop <;>
        simp [Except.map]

theorem parseChunksTR_go (d : ByteArray) (stop p : Nat) (acc : List Chunk) :
    parseChunksTR.go d stop p acc = (parseChunks d p stop).map (acc.reverse ++ ·) :=
  parseChunksTR_go_aux d stop _ p acc (Nat.le_refl _)

@[csimp] theorem parseChunks_eq_parseChunksTR : @parseChunks = @parseChunksTR := by
  funext d p stop
  rw [parseChunksTR, parseChunksTR_go]
  cases parseChunks d p stop <;> simp [Except.map]

/-- §2.4 header, returning the top-level chunks. -/
def parseRiff (d : ByteArray) : Except String (List Chunk) :=
  if 12 ≤ d.size ∧ u32 d 0 = RIFF ∧ u32 d 8 = WEBP then
    let size := u32 d 4
    if size ≤ 2 ^ 32 - 10 ∧ 8 + size ≤ d.size then parseChunks d 12 (8 + size)
    else .error "bad RIFF size"
  else .error "not a RIFF/WEBP file"

/-- Split image data `ALPH? bitstream`. -/
def frameData (core : List Chunk) : Except String (Option Chunk × Chunk) :=
  match core with
  | [b] => if isBitstream b.tag then .ok (none, b) else .error "expected bitstream chunk"
  | [a, b] =>
    if a.tag = ALPH ∧ isBitstream b.tag then .ok (some a, b)
    else .error "expected ALPH + bitstream chunks"
  | _ => .error "bad image data chunks"

/-- §2.7.1.1 'ANMF' chunk. -/
def parseFrame (d : ByteArray) (c : Chunk) : Except String FrameInfo :=
  if c.tag = ANMF ∧ 16 ≤ c.size then
    match parseChunks d (c.off + 16) (c.off + c.size) with
    | .ok sub =>
      if sub.all frameSubOk then
        match frameData (sub.filter isFrameData) with
        | .ok (alph, bits) => .ok (anmfInfo d c alph bits)
        | .error e => .error e
      else .error "known non-frame chunk inside ANMF"
    | .error e => .error e
  else .error "expected ANMF chunk"

def parseFrames (d : ByteArray) : List Chunk → Except String (List FrameInfo)
  | [] => .ok []
  | c :: cs =>
    match parseFrame d c, parseFrames d cs with
    | .ok f, .ok fs => .ok (f :: fs)
    | .error e, _ => .error e
    | _, .error e => .error e

/-- `parseFrames` with an accumulator: stops at the first invalid frame. -/
def parseFramesTR.go (d : ByteArray) : List Chunk → List FrameInfo → Except String (List FrameInfo)
  | [], acc => .ok acc.reverse
  | c :: cs, acc =>
    match parseFrame d c with
    | .ok f => go d cs (f :: acc)
    | .error e => .error e

def parseFramesTR (d : ByteArray) (cs : List Chunk) : Except String (List FrameInfo) :=
  parseFramesTR.go d cs []

theorem parseFramesTR_go (d : ByteArray) : ∀ (cs : List Chunk) (acc : List FrameInfo),
    parseFramesTR.go d cs acc = (parseFrames d cs).map (acc.reverse ++ ·)
  | [], acc => by simp [parseFramesTR.go, parseFrames, Except.map]
  | c :: cs, acc => by
    simp only [parseFramesTR.go, parseFrames]
    cases parseFrame d c with
    | error e => simp [Except.map]
    | ok f =>
      simp only [parseFramesTR_go d cs (f :: acc)]
      cases parseFrames d cs <;> simp [Except.map]

@[csimp] theorem parseFrames_eq_parseFramesTR : @parseFrames = @parseFramesTR := by
  funext d cs
  rw [parseFramesTR, parseFramesTR_go]
  cases parseFrames d cs <;> simp [Except.map]

/-- §2.7 extended format, given the 'VP8X' chunk and the chunks after it. -/
def parseExtended (d : ByteArray) (x : Chunk) (rest : List Chunk) : Except String Layout :=
  if x.size < 10 then .error "VP8X chunk too small" else
  let info := vp8xInfo d x
  if info.canvasWidth * info.canvasHeight > 2 ^ 32 - 1 then .error "canvas too large" else
  let core := (rest.filter isRecon).dropWhile (fun c => c.tag = ICCP)
  if info.animation then
    match core with
    | a :: anmfs =>
      if a.tag = ANIM ∧ 6 ≤ a.size ∧ anmfs ≠ [] then
        match parseFrames d anmfs with
        | .ok frames =>
          if frames.all (fun f => decide (frameInCanvas info f)) then
            .ok (.animated info (u32 d a.off) (u16 d (a.off + 4)) frames)
          else .error "frame outside canvas"
        | .error e => .error e
      else .error "animation needs ANIM followed by ANMF chunks"
    | [] => .error "animation needs ANIM followed by ANMF chunks"
  else
    match frameData ((rest.filter isStillRecon).dropWhile (fun c => c.tag = ICCP)) with
    | .ok (alph, bits) => .ok (.still (some info) alph bits)
    | .error e => .error e

/-- **The demuxer.** -/
def demux (d : ByteArray) : Except String Layout :=
  match parseRiff d with
  | .ok (c :: rest) =>
    if c.tag = VP8X then parseExtended d c rest
    else if isBitstream c.tag ∧ rest.filter isRecon = [] then .ok (.still none none c)
    else .error "unexpected first chunk"
  | .ok [] => .error "no chunks"
  | .error e => .error e

/-- Copy of a chunk's payload. -/
def payload (d : ByteArray) (c : Chunk) : ByteArray := d.extract c.off (c.off + c.size)

end WebP.Container

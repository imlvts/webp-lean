import WebP.Proofs.Alpha
import WebP.Anim
/-!
# In-place canvas assembly equals the pointwise definition

`compose_eq : WebP.Anim.compose = Spec.Anim.compose`. The fast version updates only each
frame's rectangle, in place; the specification recomputes every canvas byte. The proof:

* `zeros_eq`: the doubling construction is the zero canvas;
* `writePx_byte`, `rowLoop_spec`, `rectLoop_spec`: after the loops, a byte holds `g` applied to
  its pixel's *original* bytes if the pixel is in the (width-clipped) rectangle, and is
  unchanged otherwise (pixels are written once, and each write reads only its own pixel);
* `row_iff`: a row's pixel range is exactly the pixels with that row and column bounds;
* `renderFrame_eq`, `disposeFrame_eq`: byte-by-byte agreement with the specification.
-/
namespace WebP.Proofs

open WebP.Spec WebP.Spec.Anim

/-! ## Bytes -/

theorem byte_ge (d : ByteArray) (j : Nat) (h : d.size ≤ j) : byte d j = 0 := by
  unfold byte; split
  · omega
  · rfl

/-- Byte arrays are equal when their sizes and bytes are. -/
theorem byteArray_ext (a b : ByteArray) (hs : a.size = b.size)
    (hb : ∀ j < a.size, byte a j = byte b j) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  apply ByteArray.ext
  apply Array.ext
  · simpa [ByteArray.size] using hs
  · intro j h1 h2
    have := hb j (by simpa [ByteArray.size] using h1)
    rw [byte_mk, byte_mk] at this
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.getD_some] at this
    exact UInt8.toNat_inj.mp this

theorem byte_set' (out : ByteArray) (i j : Nat) (x : UInt8) :
    byte (out.set! i x) j = if j = i ∧ i < out.size then x.toNat else byte out j := by
  by_cases hi : i < out.size
  · rw [byte_set _ _ _ _ hi]; simp [hi]
  · simp only [hi, and_false, ite_false]
    obtain ⟨a⟩ := out
    have hi' : ¬ i < a.size := hi
    simp only [ByteArray.set!, byte_mk, Array.set!_eq_setIfInBounds,
      Array.setIfInBounds, hi', dite_false]

/-- The bytes of pixel `p`. -/
def px (cv : ByteArray) (p : Nat) : Nat → Nat := fun ch => byte cv (4 * p + ch)

/-- `g c t` only looks at the pixel's bytes `t ch` for `ch < 4`. -/
def PxCongr (g : Nat → (Nat → Nat) → UInt8) : Prop :=
  ∀ c (t t' : Nat → Nat), c < 4 → (∀ ch < 4, t ch = t' ch) → g c t = g c t'

/-- If no byte of pixel `q` changed, its `px` agrees on the four channels. -/
theorem px_congr (cv cv' : ByteArray) (q : Nat) (hs : cv'.size = cv.size)
    (h : ∀ j < cv.size, j / 4 = q → byte cv' j = byte cv j) :
    ∀ ch < 4, px cv' q ch = px cv q ch := by
  intro ch hch
  unfold px
  by_cases hj : 4 * q + ch < cv.size
  · exact h _ hj (by omega)
  · rw [byte_ge _ _ (by omega), byte_ge _ _ (by omega)]

/-! ## Zero canvas -/

theorem zeros_data : ∀ n, (WebP.Anim.zeros n).data = Array.replicate n 0
  | 0 => by simp [WebP.Anim.zeros]
  | n + 1 => by
    have ih := zeros_data ((n + 1) / 2)
    rw [WebP.Anim.zeros]
    split
    · rw [ByteArray.data_push, ByteArray.data_append, ih, Array.replicate_append_replicate,
        ← Array.replicate_succ]
      congr 1; omega
    · rw [ByteArray.data_append, ih, Array.replicate_append_replicate]
      congr 1; omega
decreasing_by omega

theorem zeros_eq (n : Nat) : WebP.Anim.zeros n = ⟨Array.replicate n 0⟩ := by
  apply ByteArray.ext; exact zeros_data n

/-! ## Writing pixels -/

theorem writePx_size (g : Nat → (Nat → Nat) → UInt8) (cv : ByteArray) (p : Nat) :
    (WebP.Anim.writePx g cv p).size = cv.size := by
  simp [WebP.Anim.writePx]

theorem writePx_byte (g : Nat → (Nat → Nat) → UInt8) (hg : PxCongr g) (cv : ByteArray)
    (p j : Nat) (hj : j < cv.size) :
    byte (WebP.Anim.writePx g cv p) j =
      if j / 4 = p then (g (j % 4) (px cv p)).toNat else byte cv j := by
  have ht : ∀ ch < 4, (fun ch => if ch = 0 then byte cv (4 * p) else if ch = 1 then
      byte cv (4 * p + 1) else if ch = 2 then byte cv (4 * p + 2) else byte cv (4 * p + 3)) ch =
      px cv p ch := by
    intro ch hch
    rcases (by omega : ch = 0 ∨ ch = 1 ∨ ch = 2 ∨ ch = 3) with rfl | rfl | rfl | rfl <;> rfl
  simp only [WebP.Anim.writePx, byte_set', size_set]
  by_cases hp : j / 4 = p
  · rw [ite_eq_left hp]
    rcases (by omega : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3) with h0 | h0 | h0 | h0
    · rw [h0, ← hg 0 _ _ (by decide) ht]
      have : j = 4 * p := by omega
      simp [this]; omega
    · rw [h0, ← hg 1 _ _ (by decide) ht]
      have : j = 4 * p + 1 := by omega
      simp [this]; omega
    · rw [h0, ← hg 2 _ _ (by decide) ht]
      have : j = 4 * p + 2 := by omega
      simp [this]; omega
    · rw [h0, ← hg 3 _ _ (by decide) ht]
      have : j = 4 * p + 3 := by omega
      simp [this]; omega
  · rw [ite_eq_right hp]
    have h0 : j ≠ 4 * p := by omega
    have h1 : j ≠ 4 * p + 1 := by omega
    have h2 : j ≠ 4 * p + 2 := by omega
    have h3 : j ≠ 4 * p + 3 := by omega
    simp [h0, h1, h2, h3]

/-- A row of pixels `[p, p + n)`. -/
theorem rowLoop_spec (g : Nat → Nat → (Nat → Nat) → UInt8) (hg : ∀ q, PxCongr (g q)) :
    ∀ n p (cv : ByteArray), (WebP.Anim.rowLoop g cv p n).size = cv.size ∧
      ∀ j < cv.size, byte (WebP.Anim.rowLoop g cv p n) j =
        if p ≤ j / 4 ∧ j / 4 < p + n then (g (j / 4) (j % 4) (px cv (j / 4))).toNat
        else byte cv j := by
  intro n
  induction n with
  | zero =>
    intro p cv
    refine ⟨rfl, fun j _ => ?_⟩
    simp only [WebP.Anim.rowLoop]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    intro p cv
    let cv1 := WebP.Anim.writePx (g p) cv p
    have hs1 : cv1.size = cv.size := writePx_size _ _ _
    obtain ⟨hs, hb⟩ := ih (p + 1) cv1
    simp only [WebP.Anim.rowLoop]
    refine ⟨by rw [hs, hs1], fun j hj => ?_⟩
    rw [hb j (by omega)]
    by_cases hin : p + 1 ≤ j / 4 ∧ j / 4 < p + 1 + n
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
      -- pixel `j / 4` was not touched by the write at pixel `p`
      have hpx := px_congr cv cv1 (j / 4) hs1 (fun k hk hkq => by
        rw [writePx_byte _ (hg p) _ _ _ hk, ite_eq_right (by omega)])
      rw [hg (j / 4) (j % 4) _ _ (Nat.mod_lt _ (by decide)) hpx]
    · rw [ite_eq_right hin, writePx_byte _ (hg p) _ _ _ hj]
      by_cases hp : j / 4 = p
      · rw [ite_eq_left hp, ite_eq_left (by omega), hp]
      · rw [ite_eq_right hp, ite_eq_right (by omega)]

/-- The pixels of row `y` and columns `[x0, x0 + wd)` form the range starting at `y*W + x0`. -/
theorem row_iff (W x0 wd y q : Nat) (hW : 0 < W) (hx : x0 + wd ≤ W) :
    (y * W + x0 ≤ q ∧ q < y * W + x0 + wd) ↔ (q / W = y ∧ x0 ≤ q % W ∧ q % W < x0 + wd) := by
  have hdm := Nat.div_add_mod q W
  have hm := Nat.mod_lt q hW
  constructor
  · rintro ⟨h1, h2⟩
    have hy : q / W = y := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm] at *; omega)
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
    rw [hy] at hdm
    rw [Nat.mul_comm] at hdm
    exact ⟨hy, by omega, by omega⟩
  · rintro ⟨hy, h1, h2⟩
    rw [hy, Nat.mul_comm] at hdm
    omega

/-- Rows `[y, y + n)` of the rectangle with columns `[x0, x0 + wd)`. -/
theorem rectLoop_spec (g : Nat → Nat → (Nat → Nat) → UInt8) (hg : ∀ q, PxCongr (g q))
    (W x0 wd : Nat) (hW : 0 < W) (hx : x0 + wd ≤ W) :
    ∀ n y (cv : ByteArray), (WebP.Anim.rectLoop g W x0 wd cv y n).size = cv.size ∧
      ∀ j < cv.size, byte (WebP.Anim.rectLoop g W x0 wd cv y n) j =
        if y ≤ j / 4 / W ∧ j / 4 / W < y + n ∧ x0 ≤ j / 4 % W ∧ j / 4 % W < x0 + wd then
          (g (j / 4) (j % 4) (px cv (j / 4))).toNat
        else byte cv j := by
  intro n
  induction n with
  | zero =>
    intro y cv
    refine ⟨rfl, fun j _ => ?_⟩
    simp only [WebP.Anim.rectLoop]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    intro y cv
    obtain ⟨hs1, hb1⟩ := rowLoop_spec g hg wd (y * W + x0) cv
    obtain ⟨hs, hb⟩ := ih (y + 1) (WebP.Anim.rowLoop g cv (y * W + x0) wd)
    simp only [WebP.Anim.rectLoop]
    refine ⟨by rw [hs, hs1], fun j hj => ?_⟩
    rw [hb j (by omega)]
    have hrow := row_iff W x0 wd y (j / 4) hW hx
    by_cases hin : y + 1 ≤ j / 4 / W ∧ j / 4 / W < y + 1 + n ∧ x0 ≤ j / 4 % W ∧
        j / 4 % W < x0 + wd
    · rw [ite_eq_left hin, ite_eq_left (by omega)]
      -- pixel `j / 4` is below row `y`, so the row loop left it alone
      have hpx := px_congr cv _ (j / 4) hs1 (fun k hk hkq => by
        rw [hb1 k hk, ite_eq_right (by rw [hkq, hrow]; omega)])
      rw [hg (j / 4) (j % 4) _ _ (Nat.mod_lt _ (by decide)) hpx]
    · rw [ite_eq_right hin, hb1 j hj]
      by_cases hy : j / 4 / W = y ∧ x0 ≤ j / 4 % W ∧ j / 4 % W < x0 + wd
      · rw [ite_eq_left (hrow.mpr hy), ite_eq_left (by omega)]
      · rw [ite_eq_right (fun h => hy (hrow.mp h)), ite_eq_right (by omega)]

theorem rectLoop_zero (g : Nat → Nat → (Nat → Nat) → UInt8) (W x0 : Nat) :
    ∀ n y (cv : ByteArray), WebP.Anim.rectLoop g W x0 0 cv y n = cv := by
  intro n
  induction n with
  | zero => intro y cv; rfl
  | succ n ih => intro y cv; simp only [WebP.Anim.rectLoop, WebP.Anim.rowLoop, ih]

/-- The frame rectangle, clipped to width `W`, is exactly where `inRect` holds. -/
theorem fillRect_spec (g : Nat → Nat → (Nat → Nat) → UInt8) (hg : ∀ q, PxCongr (g q))
    (W : Nat) (hW : 0 < W) (f : FrameInfo) (cv : ByteArray) :
    (WebP.Anim.fillRect g W f cv).size = cv.size ∧
      ∀ j < cv.size, byte (WebP.Anim.fillRect g W f cv) j =
        if inRect f (j / 4 % W) (j / 4 / W) then (g (j / 4) (j % 4) (px cv (j / 4))).toNat
        else byte cv j := by
  unfold WebP.Anim.fillRect
  have hm := fun j => Nat.mod_lt (j / 4) hW
  by_cases hfx : f.x < W
  · obtain ⟨hs, hb⟩ := rectLoop_spec g hg W f.x (min (f.x + f.width) W - f.x) hW
      (by omega) f.height f.y cv
    refine ⟨hs, fun j hj => ?_⟩
    rw [hb j hj]
    have := hm j
    congr 1
    simp only [inRect, Bool.and_eq_true, decide_eq_true_eq, eq_iff_iff]
    omega
  · have hwd : min (f.x + f.width) W - f.x = 0 := by omega
    rw [hwd, rectLoop_zero]
    refine ⟨rfl, fun j _ => ?_⟩
    have := hm j
    rw [ite_eq_right]
    simp only [inRect, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-! ## Frames -/

theorem spec_renderFrame_size (W : Nat) (canvas : ByteArray) (f : FrameInfo) (img : ByteArray) :
    (Spec.Anim.renderFrame W canvas f img).size = canvas.size := by
  unfold Spec.Anim.renderFrame; exact Array.size_ofFn

theorem spec_disposeFrame_size (W : Nat) (canvas : ByteArray) (f : FrameInfo) :
    (Spec.Anim.disposeFrame W canvas f).size = canvas.size := by
  unfold Spec.Anim.disposeFrame; exact Array.size_ofFn

theorem byte_getElem (canvas : ByteArray) (j : Nat) (hj : j < canvas.size) :
    canvas[j].toNat = byte canvas j := by
  unfold byte; rw [dite_eq_left hj]

theorem spec_renderFrame_byte (W : Nat) (canvas : ByteArray) (f : FrameInfo) (img : ByteArray)
    (j : Nat) (hj : j < canvas.size) :
    byte (Spec.Anim.renderFrame W canvas f img) j =
      if inRect f (j / 4 % W) (j / 4 / W) then
        (WebP.Anim.renderByte W f img (j / 4) (j % 4) (px canvas (j / 4))).toNat
      else byte canvas j := by
  unfold Spec.Anim.renderFrame
  rw [byte_mk]
  have hj' : j < (Array.ofFn (n := canvas.size) fun _ => (0 : UInt8)).size := by simpa using hj
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj, dite_eq_left, Option.getD_some]
  split
  · rfl
  · exact byte_getElem canvas j hj

theorem spec_disposeFrame_byte (W : Nat) (canvas : ByteArray) (f : FrameInfo) (j : Nat)
    (hj : j < canvas.size) :
    byte (Spec.Anim.disposeFrame W canvas f) j =
      if inRect f (j / 4 % W) (j / 4 / W) then 0 else byte canvas j := by
  unfold Spec.Anim.disposeFrame
  rw [byte_mk]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hj, dite_eq_left, Option.getD_some]
  split
  · rfl
  · exact byte_getElem canvas j hj

theorem renderByte_congr (W : Nat) (f : FrameInfo) (img : ByteArray) (p : Nat) :
    PxCongr (WebP.Anim.renderByte W f img p) := by
  intro c t t' hc ht
  unfold WebP.Anim.renderByte
  simp only [ht c hc, ht 3 (by decide)]

theorem renderFrame_eq : WebP.Anim.renderFrame = Spec.Anim.renderFrame := by
  funext W canvas f img
  unfold WebP.Anim.renderFrame
  split
  · rfl
  · rename_i hW
    obtain ⟨hs, hb⟩ := fillRect_spec (WebP.Anim.renderByte W f img)
      (renderByte_congr W f img) W (by omega) f canvas
    apply byteArray_ext _ _ (by rw [hs, spec_renderFrame_size])
    intro j hj
    rw [hs] at hj
    rw [hb j hj, spec_renderFrame_byte W canvas f img j hj]

theorem disposeFrame_eq : WebP.Anim.disposeFrame = Spec.Anim.disposeFrame := by
  funext W canvas f
  unfold WebP.Anim.disposeFrame
  split
  · rfl
  · rename_i hW
    obtain ⟨hs, hb⟩ := fillRect_spec (fun _ _ _ => 0) (fun _ _ _ _ _ _ => rfl) W (by omega)
      f canvas
    apply byteArray_ext _ _ (by rw [hs, spec_disposeFrame_size])
    intro j hj
    rw [hs] at hj
    rw [hb j hj, spec_disposeFrame_byte W canvas f j hj]
    rfl

theorem compose_go_eq (W : Nat) : ∀ (canvas : ByteArray) (prev : Option FrameInfo)
    (l : List (FrameInfo × ByteArray)) (acc : List ByteArray),
    WebP.Anim.compose.go W canvas prev l acc = acc.reverse ++ Spec.Anim.compose.go W canvas prev l
  | _, _, [], acc => by simp [WebP.Anim.compose.go, Spec.Anim.compose.go]
  | canvas, prev, (f, img) :: rest, acc => by
    cases prev <;> simp [WebP.Anim.compose.go, Spec.Anim.compose.go, renderFrame_eq,
      disposeFrame_eq, compose_go_eq]

/-- **In-place canvas assembly computes the specified canvases.** -/
theorem compose_eq : WebP.Anim.compose = Spec.Anim.compose := by
  funext W H frames
  unfold WebP.Anim.compose Spec.Anim.compose
  rw [zeros_eq, compose_go_eq]; rfl

end WebP.Proofs

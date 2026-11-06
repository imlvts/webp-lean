import WebP.Proofs.Decode
import WebP.Info
/-!
# Metadata agrees with decoding

* `info_of_decode`: if `WebP.decode d = .ok o`, then `WebP.info d = .ok i` and `i` reports the
  same canvas size, animation/alpha/lossy flags, loop count, background color and frame
  durations as `o` (`InfoMatches i o`).
* `info_of_decodes`: the same for the semantics `Spec.Decodes Spec.lossy`.
* `info_wellFormed`: `info` only accepts well-formed containers (`Spec.Demux`).
-/
namespace WebP.Proofs

open WebP WebP.Spec

/-- `i` describes the decoding result `o`. -/
structure InfoMatches (i : Info) (o : Output) : Prop where
  width : i.width = o.width
  height : i.height = o.height
  animated : i.animated = o.animated
  hasAlpha : i.hasAlpha = o.hasAlpha
  lossy : i.lossy = o.lossy
  loopCount : i.loopCount = o.loopCount
  background : i.background = o.background
  durations : i.frames.map (·.duration) = o.frames.map (·.1)

/-- A decoded lossless image has the size and hint of its header. -/
theorem vp8l_readHeaderOnly_of_decode (p : ByteArray) (img : Spec.VP8L.Image)
    (h : Spec.VP8L.decode p = .ok img) :
    Spec.VP8L.readHeaderOnly p = .ok (img.width, img.height, img.alphaHint) := by
  unfold Spec.VP8L.decode Spec.VP8L.decodeWith at h
  unfold Spec.VP8L.readHeaderOnly
  simp only [StateT.run', bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure, Functor.map, Except.map] at h ⊢
  cases hr : Spec.VP8L.readHeader Spec.VP8L.specPrims p 0 with
  | error e => simp [hr] at h
  | ok r =>
    obtain ⟨⟨w, hh, a⟩, s⟩ := r
    simp only [hr] at h ⊢
    cases hs : Spec.VP8L.decodeImageStream Spec.VP8L.specPrims p w hh s with
    | error e => simp [hs] at h
    | ok r' => simp only [hs, Except.ok.injEq] at h; cases h; rfl

/-- A decoded lossy image has the size of its frame header. -/
theorem vp8_decodeHeaders_of_decode (p : ByteArray) (img : RGBAImage)
    (h : vp8Decode p = .ok img) :
    ∃ H, Spec.VP8.decodeHeaders VP8.fastPrims p = .ok H ∧ H.hdr.w = img.width ∧
      H.hdr.h = img.height := by
  unfold vp8Decode WebP.VP8.decodeFrame Spec.VP8.decodeWith at h
  cases hH : Spec.VP8.decodeHeaders VP8.fastPrims p with
  | error e => simp [hH, bind, Except.bind, Except.map] at h
  | ok H =>
    simp only [hH, bind, Except.bind, pure, Except.pure, Except.map, Except.ok.injEq] at h
    exact ⟨H, rfl, by rw [← h], by rw [← h]⟩

/-- A decoded image has the size given by `bitstreamHeader`. -/
theorem bitstreamHeader_of_decodeImage (d : ByteArray) (alph : Option Chunk) (bits : Chunk)
    (img : RGBAImage) (h : decodeImage (specComponents vp8Decode) d alph bits = .ok img) :
    ∃ a, bitstreamHeader d bits = .ok (img.width, img.height, a) ∧
      (bits.tag ≠ VP8L → a = false) := by
  unfold decodeImage at h
  by_cases ht : bits.tag = VP8L
  · simp only [ht, ite_true, specComponents, bind, Except.bind, pure, Except.pure] at h
    cases hv : Spec.VP8L.decode (payload d bits) with
    | error e => simp [hv] at h
    | ok im =>
      simp only [hv, Except.ok.injEq] at h
      subst h
      exact ⟨im.alphaHint, by simp [bitstreamHeader, ht, vp8l_readHeaderOnly_of_decode _ _ hv],
        fun h' => absurd ht h'⟩
  · simp only [ht, ite_false, specComponents, bind, Except.bind, pure, Except.pure] at h
    cases hv : vp8Decode (payload d bits) with
    | error e => simp [hv] at h
    | ok im =>
      obtain ⟨H, hH, hw, hh⟩ := vp8_decodeHeaders_of_decode _ _ hv
      have hdim : img.width = im.width ∧ img.height = im.height := by
        simp only [hv] at h
        cases alph with
        | none => simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
        | some a =>
          simp only at h
          split at h
          · simp at h
          · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
      refine ⟨false, ?_, fun _ => rfl⟩
      simp [bitstreamHeader, ht, hH, bind, Except.bind, pure, Except.pure, hw, hh, hdim.1,
        hdim.2]

theorem compose_go_length (W : Nat) : ∀ (canvas : ByteArray) (prev : Option FrameInfo)
    (l : List (FrameInfo × ByteArray)), (Anim.compose.go W canvas prev l).length = l.length
  | _, _, [] => rfl
  | canvas, prev, (f, img) :: rest => by
    simp only [Anim.compose.go, List.length_cons, compose_go_length]

theorem compose_length (W H : Nat) (l : List (FrameInfo × ByteArray)) :
    (Anim.compose W H l).length = l.length := compose_go_length W _ _ l

theorem animFrames_of_decodeFrames (d : ByteArray) : ∀ (frames : List FrameInfo)
    (dec : List (FrameInfo × ByteArray)),
    decodeFrames (specComponents vp8Decode) d frames = .ok dec →
    ∃ fs, animFrames d frames = .ok fs ∧ fs.map (·.duration) = frames.map (·.duration) ∧
      dec.length = frames.length
  | [], dec, h => by
    simp only [decodeFrames, Except.ok.injEq] at h; subst h
    exact ⟨[], rfl, rfl, rfl⟩
  | f :: fs, dec, h => by
    simp only [decodeFrames, bind, Except.bind] at h
    cases hi : decodeImage (specComponents vp8Decode) d f.alph f.bits with
    | error e => simp [hi] at h
    | ok img =>
      obtain ⟨a, hb, -⟩ := bitstreamHeader_of_decodeImage d f.alph f.bits img hi
      simp only [hi] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hsz
        simp only [ne_eq, not_or, Decidable.not_not] at hsz
        cases hr : decodeFrames (specComponents vp8Decode) d fs with
        | error e => simp [hr] at h
        | ok rest =>
          simp only [hr, pure, Except.pure, Except.ok.injEq] at h
          subst h
          obtain ⟨ms, hms, hdur, hlen⟩ := animFrames_of_decodeFrames d fs rest hr
          simp only [animFrames, hb, bind, Except.bind, hsz.1, hsz.2, ne_eq, not_true_eq_false,
            or_self, ite_false, hms, pure, Except.pure]
          exact ⟨_, rfl, by simp [hdur], by simp [hlen]⟩

/-- Metadata of a layout agrees with its decoding. -/
theorem infoOfLayout_of_decodeLayout (d : ByteArray) (L : Layout) (o : Output)
    (h : decodeLayout (specComponents vp8Decode) d L = .ok o) :
    ∃ i, infoOfLayout d L = .ok i ∧ InfoMatches i o := by
  cases L with
  | still vp8x alph bits =>
    simp only [decodeLayout, bind, Except.bind] at h
    cases hi : decodeImage (specComponents vp8Decode) d alph bits with
    | error e => simp [hi] at h
    | ok img =>
      obtain ⟨a, hb, ha⟩ := bitstreamHeader_of_decodeImage d alph bits img hi
      simp only [hi] at h
      cases vp8x with
      | none =>
        have hro : bits.tag = VP8L →
            Spec.VP8L.readHeaderOnly (payload d bits) = .ok (img.width, img.height, a) :=
          fun ht => by simpa [bitstreamHeader, ht] using hb
        simp only [infoOfLayout, hb, bind, Except.bind, pure, Except.pure]
        refine ⟨_, rfl, ?_⟩
        by_cases ht : bits.tag = VP8L
        · simp only [ht, ite_true, hro ht, pure, Except.pure, Except.ok.injEq] at h
          subst h; constructor <;> simp [ht]
        · simp only [ht, ite_false, pure, Except.pure, Except.ok.injEq] at h
          subst h; constructor <;> simp [ha ht]
      | some x =>
        simp only at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hsz
          simp only [ne_eq, not_or, Decidable.not_not] at hsz
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [infoOfLayout, hb, bind, Except.bind, hsz.1, hsz.2, ne_eq,
            not_true_eq_false, or_self, ite_false, pure, Except.pure]
          refine ⟨_, rfl, ?_⟩
          constructor <;> simp
  | animated x bg loops frames =>
    simp only [decodeLayout, bind, Except.bind] at h
    cases hf : decodeFrames (specComponents vp8Decode) d frames with
    | error e => simp [hf] at h
    | ok dec =>
      obtain ⟨fs, hfs, hdur, hlen⟩ := animFrames_of_decodeFrames d frames dec hf
      simp only [hf, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [infoOfLayout, hfs, bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_⟩
      constructor <;> try rfl
      simp only
      rw [List.map_fst_zip (by simp [compose_length, hlen]), hdur]

/-- **Metadata agrees with decoding**: whenever the decoder succeeds, `info` succeeds and
reports the same canvas size, flags, loop count, background color and frame durations. -/
theorem info_of_decode (d : ByteArray) (o : Output) (h : WebP.decode d = .ok o) :
    ∃ i, WebP.info d = .ok i ∧ InfoMatches i o := by
  unfold WebP.decode WebP.decodeWith at h
  rw [implComponents_eq] at h
  cases hL : Container.demux d with
  | error e => simp [hL, bind, Except.bind] at h
  | ok L =>
    simp only [hL, bind, Except.bind] at h
    obtain ⟨i, hi, hm⟩ := infoOfLayout_of_decodeLayout d L o h
    -- `demux` succeeded, so the chunk list parses
    obtain ⟨cs, hcs⟩ : ∃ cs, Container.parseRiff d = .ok cs := by
      unfold Container.demux at hL
      cases hp : Container.parseRiff d with
      | ok cs => exact ⟨cs, rfl⟩
      | error e => simp [hp] at hL
    unfold WebP.info
    simp only [hL, hi, hcs, bind, Except.bind, pure, Except.pure]
    split
    · exact ⟨_, rfl, ⟨hm.1, hm.2, hm.3, hm.4, hm.5, hm.6, hm.7, hm.8⟩⟩
    · exact ⟨i, rfl, hm⟩

/-- The same, for the WebP semantics with the RFC 6386 lossy decoding. -/
theorem info_of_decodes (d : ByteArray) (o : Output) (h : Spec.Decodes Spec.lossy d o) :
    ∃ i, WebP.info d = .ok i ∧ InfoMatches i o :=
  info_of_decode d o ((decode_iff' d o).mpr h)

/-- `info` only accepts well-formed WebP containers. -/
theorem info_wellFormed (d : ByteArray) (i : Info) (h : WebP.info d = .ok i) :
    ∃ L, Spec.Demux d L := by
  unfold WebP.info at h
  cases hL : Container.demux d with
  | error e => simp [hL, bind, Except.bind] at h
  | ok L => exact ⟨L, (demux_iff d L).mp hL⟩

end WebP.Proofs

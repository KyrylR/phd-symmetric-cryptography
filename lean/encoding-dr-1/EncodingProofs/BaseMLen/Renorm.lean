import EncodingProofs.BaseMLen.Prefix
import Mathlib

/-!
Renormalization lemmas for the length-delimited base-`m` transducer.

This file isolates the arithmetic facts about the normalization window and proves
that the encoder-side and decoder-side renormalization procedures are inverse on
states in the valid window. These lemmas are the bridge between prefix
correctness and payload correctness.
-/

namespace EncodingProofs.BaseMLen

/-! All declarations in `namespace Params` are renormalization facts for a fixed
supported parameter package `p`. Theorems here explain both why renormalization
is safe inside the bounded `p.width`-bit state space and how the two procedures
cancel each other. -/
namespace Params

/-- The decoder lower bound is exactly divisible by `256`. This is true because
`decoderLowerBound` was defined as a multiple of `256`, and the theorem is used
to replace a floor-division expression with an exact equality in later payload
bounds. -/
theorem decoderLowerBound_div_mul_256 (p : Params) :
    (p.decoderLowerBound / 256) * 256 = p.decoderLowerBound := by
  unfold Params.decoderLowerBound EncodingProofs.BaseMLen.decoderLowerBound
  simp [Nat.mul_comm]

/-- Arithmetic relation between the encoder threshold and the decoder window:
`T * 256 = L * m`.

How the proof works: unfold `encoderThreshold`, rewrite
`decoderLowerBound / 256` using `decoderLowerBound_div_256`, and simplify the
resulting polynomial identity by `ring`. This equality is the key link between
the byte alphabet size `256` and the base-`m` normalization window. -/
theorem encoderThreshold_mul_256 (p : Params) :
    p.encoderThreshold * 256 = p.decoderLowerBound * p.modulus := by
  unfold Params.encoderThreshold EncodingProofs.BaseMLen.encoderThreshold
  rw [EncodingProofs.BaseMLen.decoderLowerBound_div_256 p.width p.modulus]
  unfold Params.decoderLowerBound EncodingProofs.BaseMLen.decoderLowerBound
  ring1

/-- The encoder threshold lies below the upper edge of the decoder window:
`T ≤ L * m`.

How the proof works: rewrite `T` using `encoderThreshold_mul_256`, then use the
trivial inequality `1 ≤ 256` to conclude `T ≤ T * 256 = L * m`. This upper bound
is later used when proving that encoded payload states remain in the valid
window. -/
theorem encoderThreshold_lt_mul (p : Params) :
    p.encoderThreshold ≤ p.decoderLowerBound * p.modulus := by
  rw [← encoderThreshold_mul_256 p]
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left p.encoderThreshold (show 1 ≤ (256 : Nat) by decide)

/-- The entire normalization window fits below the largest representable word
value: `L * m ≤ wordMax w`.

How the proof works: unfold `decoderLowerBound` and compare
`((wordMax w / m) / 256 * 256) * m` with `(wordMax w / m) * m`, then apply the
basic division inequality `(wordMax w / m) * m ≤ wordMax w`. This is the safety
theorem showing that the window construction respects the global state bound. -/
theorem decoderLowerBound_mul_modulus_le_wordMax (p : Params) :
    p.decoderLowerBound * p.modulus ≤ wordMax p.width := by
  unfold Params.decoderLowerBound EncodingProofs.BaseMLen.decoderLowerBound
  calc
    ((wordMax p.width / p.modulus) / 256 * 256) * p.modulus
        ≤ (wordMax p.width / p.modulus) * p.modulus := by
          exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
    _ ≤ wordMax p.width := Nat.div_mul_le_self _ _

/-- Unfolding lemma for the recursive branch of `renormEncode`. It records the
defining equation used whenever the input state satisfies `T ≤ x`. -/
theorem renormEncode_eq_of_ge (p : Params) {x : Nat} (h : p.encoderThreshold ≤ x) :
    renormEncode p x =
      let digit := p.natDigit x
      let rest := renormEncode p (x / p.modulus)
      (rest.1, rest.2 ++ [digit]) := by
  rw [Params.renormEncode.eq_1, dif_pos h]

/-- Unfolding lemma for the terminal branch of `renormEncode`. It records that no
digits are emitted once the state is already below the encoder threshold. -/
theorem renormEncode_eq_of_lt (p : Params) {x : Nat} (h : x < p.encoderThreshold) :
    renormEncode p x = (x, []) := by
  rw [Params.renormEncode.eq_1, dif_neg (not_le_of_gt h)]

/-- Unfolding lemma for the successful branch of `renormDecode`. If the current
state is already in the decoder window, decoding stops immediately and returns
the untouched suffix. -/
theorem renormDecode_eq_of_ge (p : Params) {x : Nat} {digits : List (Digit p.modulus)}
    (h : p.decoderLowerBound ≤ x) :
    renormDecode p x digits = .ok (x, digits) := by
  conv_lhs => unfold Params.renormDecode
  simp [h]

/-- Unfolding lemma for the consuming branch of `renormDecode`. If the state is
below `L`, decoding must read one more payload digit and update
`x <- x * m + d`. -/
theorem renormDecode_eq_of_lt (p : Params) {x : Nat} {digits : List (Digit p.modulus)}
    (h : x < p.decoderLowerBound) :
    renormDecode p x digits =
      match digits with
      | [] => .error .notEnoughPayloadDigits
      | d :: rest => renormDecode p (x * p.modulus + d.1) rest := by
  conv_lhs => unfold Params.renormDecode
  simp [not_le_of_gt h]
  rfl

/-- After encoder-side renormalization, the returned state is always below the
encoder threshold.

How the proof works: use strong induction on `x`. In the recursive case
`T ≤ x`, the next state is `x / m`, and the strict decrease `x / m < x` follows
from `x > 0` and `m > 1`; the induction hypothesis then applies to the smaller
quotient. In the terminal case, the conclusion is exactly the branch condition
`x < T`. -/
theorem renormEncode_fst_lt_threshold (p : Params) :
    ∀ x : Nat, (renormEncode p x).1 < p.encoderThreshold := by
  intro x
  refine Nat.strong_induction_on x ?_
  intro x ih
  by_cases h : p.encoderThreshold ≤ x
  · have hm : 1 < p.modulus := lt_of_lt_of_le (by decide : 1 < 2) p.modulus_ge_two
    have hx : 0 < x := lt_of_lt_of_le p.encoderThreshold_pos h
    have hdiv : x / p.modulus < x := Nat.div_lt_self hx hm
    rw [renormEncode_eq_of_ge p h]
    simpa using ih (x / p.modulus) hdiv
  · have hlt : x < p.encoderThreshold := lt_of_not_ge h
    rw [renormEncode_eq_of_lt p hlt]
    exact hlt

/-- Lower-bound preservation for encoder-side renormalization. If the input state
satisfies `L / 256 ≤ x`, then the returned normalized state still satisfies
`L / 256 ≤ (renormEncode p x).1`.

How the proof works: again use strong induction on `x`. In the recursive branch,
`T ≤ x` implies `L / 256 ≤ x / m` by rearranging the definition
`T = (L / 256) * m`, so the induction hypothesis transfers the lower bound to
the quotient. In the terminal branch, the result is immediate. This theorem is
what later lets payload encoding prove `L ≤ 256 * q + b`. -/
theorem renormEncode_fst_ge_chunk (p : Params) :
    ∀ x : Nat, p.decoderLowerBound / 256 ≤ x → p.decoderLowerBound / 256 ≤ (renormEncode p x).1 := by
  intro x
  refine Nat.strong_induction_on x ?_
  intro x ih hx
  by_cases h : p.encoderThreshold ≤ x
  · have hm : p.decoderLowerBound / 256 ≤ x / p.modulus := by
      exact (Nat.le_div_iff_mul_le p.modulus_pos).2 <| by
        simpa [Params.encoderThreshold] using h
    have hm' : x / p.modulus < x := by
      have hmod : 1 < p.modulus := lt_of_lt_of_le (by decide : 1 < 2) p.modulus_ge_two
      have hxpos : 0 < x := lt_of_lt_of_le p.encoderThreshold_pos h
      exact Nat.div_lt_self hxpos hmod
    rw [renormEncode_eq_of_ge p h]
    simpa using ih (x / p.modulus) hm' hm
  · have hlt : x < p.encoderThreshold := lt_of_not_ge h
    rw [renormEncode_eq_of_lt p hlt]
    exact hx

/-- Appending the digits emitted by `renormEncode` in front of a suffix does not
change the effect of `renormDecode` on a state strictly below `L`.

How the proof works: use strong induction on `x`. In the recursive branch,
unfold `renormEncode`, move the final emitted digit to the head of the suffix,
apply the induction hypothesis to `x / m`, and then reconstruct the original
state with the Euclidean division identity
`x = (x / m) * m + (x % m)`. Since `natDigit x = x % m`, the decoder step
`(x / m) * m + natDigit x` recovers `x`. In the terminal branch, no digits were
emitted, so the statement is immediate. This lemma is the technical heart of the
renormalization roundtrip proof. -/
theorem renormDecode_append_encode_below (p : Params) :
    ∀ {x : Nat}, x < p.decoderLowerBound →
      ∀ rest : List (Digit p.modulus),
        renormDecode p (renormEncode p x).1 ((renormEncode p x).2 ++ rest) =
          renormDecode p x rest := by
  intro x
  refine Nat.strong_induction_on x ?_
  intro x ih hx rest
  by_cases henc : p.encoderThreshold ≤ x
  · have hdiv_lt_x : x / p.modulus < x := by
      have hm : 1 < p.modulus := lt_of_lt_of_le (by decide : 1 < 2) p.modulus_ge_two
      have hxpos : 0 < x := lt_of_lt_of_le p.encoderThreshold_pos henc
      exact Nat.div_lt_self hxpos hm
    have hdiv_lt_bound : x / p.modulus < p.decoderLowerBound := by
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hx
    have hrec :=
      ih (x / p.modulus) hdiv_lt_x hdiv_lt_bound (p.natDigit x :: rest)
    calc
      renormDecode p (renormEncode p x).1 ((renormEncode p x).2 ++ rest)
          = renormDecode p (renormEncode p (x / p.modulus)).1
              ((renormEncode p (x / p.modulus)).2 ++ p.natDigit x :: rest) := by
                rw [renormEncode_eq_of_ge p henc]
                change
                  renormDecode p (renormEncode p (x / p.modulus)).1
                    (((renormEncode p (x / p.modulus)).2 ++ [p.natDigit x]) ++ rest) =
                    renormDecode p (renormEncode p (x / p.modulus)).1
                      ((renormEncode p (x / p.modulus)).2 ++ p.natDigit x :: rest)
                simp [List.append_assoc]
      _ = renormDecode p (x / p.modulus) (p.natDigit x :: rest) := hrec
      _ = renormDecode p ((x / p.modulus) * p.modulus + (p.natDigit x).1) rest := by
            simpa using
              (renormDecode_eq_of_lt p (digits := p.natDigit x :: rest) hdiv_lt_bound)
      _ = renormDecode p x rest := by
            rw [show (x / p.modulus) * p.modulus + (p.natDigit x).1 = x by
              simpa [Params.natDigit, Nat.mul_comm] using (Nat.div_add_mod x p.modulus)]
  · have hlt : x < p.encoderThreshold := lt_of_not_ge henc
    rw [renormEncode_eq_of_lt p hlt]
    simp

/-- Restatement of `renormDecode_eq_of_ge` under a name used by later files. It
exists to make subsequent proofs read in terms of successful decoder outcomes
rather than unfolding lemmas. -/
theorem renormDecode_ok_of_ge (p : Params) {x : Nat} {rest : List (Digit p.modulus)}
    (h : p.decoderLowerBound ≤ x) :
    renormDecode p x rest = .ok (x, rest) := by
  exact renormDecode_eq_of_ge p h

/-- Main renormalization roundtrip theorem with an arbitrary suffix. If
`x ∈ [L, L * m)`, then decoding the digits emitted by `renormEncode` restores
the original state and leaves the extra suffix untouched.

How the proof works: split on whether `renormEncode` emits at least one digit.
If `T ≤ x`, rewrite the encoder output, reduce to the smaller state `x / m`,
use `x < L * m` to show `x / m < L`, apply
`renormDecode_append_encode_below`, and finish with the identity
`x = (x / m) * m + (x % m)`. If `x < T`, `renormEncode` emits nothing and
`renormDecode` succeeds immediately because `x ≥ L`. -/
theorem renorm_roundtrip_with_suffix (p : Params) :
    ∀ {x : Nat},
      p.decoderLowerBound ≤ x →
      x < p.decoderLowerBound * p.modulus →
      ∀ rest : List (Digit p.modulus),
        renormDecode p (renormEncode p x).1 ((renormEncode p x).2 ++ rest) = .ok (x, rest) := by
  intro x hlower hupper rest
  by_cases henc : p.encoderThreshold ≤ x
  · have hdiv_lt_bound : x / p.modulus < p.decoderLowerBound := by
      exact (Nat.div_lt_iff_lt_mul p.modulus_pos).2 <| by
        simpa [Nat.mul_comm] using hupper
    calc
      renormDecode p (renormEncode p x).1 ((renormEncode p x).2 ++ rest)
          = renormDecode p (renormEncode p (x / p.modulus)).1
              ((renormEncode p (x / p.modulus)).2 ++ p.natDigit x :: rest) := by
                rw [renormEncode_eq_of_ge p henc]
                change
                  renormDecode p (renormEncode p (x / p.modulus)).1
                    (((renormEncode p (x / p.modulus)).2 ++ [p.natDigit x]) ++ rest) =
                    renormDecode p (renormEncode p (x / p.modulus)).1
                      ((renormEncode p (x / p.modulus)).2 ++ p.natDigit x :: rest)
                simp [List.append_assoc]
      _ = renormDecode p (x / p.modulus) (p.natDigit x :: rest) := by
            exact renormDecode_append_encode_below p hdiv_lt_bound (p.natDigit x :: rest)
      _ = renormDecode p ((x / p.modulus) * p.modulus + (p.natDigit x).1) rest := by
            simpa using
              (renormDecode_eq_of_lt p (digits := p.natDigit x :: rest) hdiv_lt_bound)
      _ = renormDecode p x rest := by
            rw [show (x / p.modulus) * p.modulus + (p.natDigit x).1 = x by
              simpa [Params.natDigit, Nat.mul_comm] using (Nat.div_add_mod x p.modulus)]
      _ = .ok (x, rest) := by
            exact renormDecode_eq_of_ge p hlower
  · have hlt : x < p.encoderThreshold := lt_of_not_ge henc
    rw [renormEncode_eq_of_lt p hlt]
    simp
    exact renormDecode_eq_of_ge p hlower

/-- Alias of `renorm_roundtrip_with_suffix` under a window-oriented name. Later
proofs use this theorem to emphasize that the hypothesis is exactly
`x ∈ [L, L * m)`. -/
theorem renormDecode_encode_window_rest (p : Params) :
    ∀ {x : Nat},
      p.decoderLowerBound ≤ x →
      x < p.decoderLowerBound * p.modulus →
      ∀ rest : List (Digit p.modulus),
        renormDecode p (renormEncode p x).1 ((renormEncode p x).2 ++ rest) = .ok (x, rest) :=
  renorm_roundtrip_with_suffix p

/-- Empty-suffix specialization of `renorm_roundtrip_with_suffix`. This is the
form used when reasoning about a self-contained renormalization fragment. -/
theorem renorm_roundtrip (p : Params) :
    ∀ {x : Nat},
      p.decoderLowerBound ≤ x →
      x < p.decoderLowerBound * p.modulus →
      renormDecode p (renormEncode p x).1 (renormEncode p x).2 = .ok (x, []) := by
  intro x hlower hupper
  simpa using renorm_roundtrip_with_suffix p hlower hupper []

/-- Alias of `renorm_roundtrip` under the window-oriented name used by the
payload layer. -/
theorem renormDecode_encode_window (p : Params) :
    ∀ {x : Nat},
      p.decoderLowerBound ≤ x →
      x < p.decoderLowerBound * p.modulus →
      renormDecode p (renormEncode p x).1 (renormEncode p x).2 = .ok (x, []) :=
  renorm_roundtrip p

end Params

end EncodingProofs.BaseMLen

import Mathlib

/-!
Core parameters for the width-parametric length-delimited base-`m` byte
encoder/decoder.

This file defines the bounded word model `Fin (2^w)`, the normalization
constants derived from a word width `w`, and the arithmetic facts needed by the
later prefix, renormalization, payload, and stream proofs.

The declarations are intentionally split into two layers:

* raw facts about a word width `w` and a modulus `m`;
* bundled facts for `p : Params`, so later files do not have to repeat side
  conditions such as `SupportedModulus p.width p.modulus`.
-/

namespace EncodingProofs.BaseMLen

/-- Exclusive upper bound on unsigned `w`-bit values. We use this as the common
cap for prefix values, payload states, and encoded lengths. -/
def wordBound (w : Nat) : Nat := 2 ^ w

/-- Largest unsigned `w`-bit value. This is the top value allowed for states and
the quantity used to derive safe normalization bounds. -/
def wordMax (w : Nat) : Nat := wordBound w - 1

/-- A byte, represented as a natural number in `[0, 256)`. We keep the type
explicit because the core development works on bytes rather than text. -/
abbrev Byte := Fin 256

/-- A base-`m` digit, represented as a natural number in `[0, m)`. This models
the residue symbols emitted by the encoder and consumed by the decoder. -/
abbrev Digit (m : Nat) := Fin m

/-- An unsigned `w`-bit value, represented as a natural number in `[0, 2^w)`.
This is the type used for fixed-width prefix values after decoding. -/
abbrev WordVal (w : Nat) := Fin (wordBound w)

/-- Lower edge `L` of the normalized decoder state window for the byte-wise
transducer. It is the largest multiple of `256` such that `L * m ≤ wordMax w`,
which is exactly why later byte updates can stay inside the `w`-bit state
space. -/
def decoderLowerBound (w m : Nat) : Nat := ((wordMax w / m) / 256) * 256

/-- Encoder renormalization threshold `T`. Before absorbing a byte, the encoder
emits base-`m` digits until the state is below `T`; then the byte update
`x <- 256 * x + b` stays within the normalized window. -/
def encoderThreshold (w m : Nat) : Nat := (decoderLowerBound w m / 256) * m

/-- Supported moduli for the byte-wise transducer. We require `m ≥ 2` and
`decoderLowerBound w m ≥ 256`, so the normalization window is nontrivial and
compatible with one-byte updates. This predicate formalizes the paper's phrase
"moduli for which the transducer parameters can be instantiated." -/
def SupportedModulus (w m : Nat) : Prop := 2 ≤ m ∧ 256 ≤ decoderLowerBound w m

/-- `2^w` is monotone in `w`.

This theorem exists because later width-lifting arguments need to compare the
bounded value spaces for different word sizes. The proof is a direct
specialization of `Nat.pow_le_pow_right` to the base `2`. -/
theorem wordBound_monotone : Monotone wordBound := by
  intro w₁ w₂ hw
  simpa [wordBound] using Nat.pow_le_pow_right Nat.zero_lt_two hw

/-- Positivity of `wordBound`.

This lemma is used whenever later arithmetic wants to treat `2^w` as a genuine
nonzero modulus or upper bound rather than merely a symbolic expression. The
proof is immediate from the definition `wordBound w = 2^w`. -/
theorem wordBound_pos (w : Nat) : 0 < wordBound w := by
  simp [wordBound]

/-- `2^w - 1` is monotone in `w`.

This theorem packages the fact that enlarging the word width can only enlarge
the largest representable value. The proof first applies `wordBound_monotone`
and then subtracts `1` from both sides using `Nat.sub_le_sub_right`. -/
theorem wordMax_monotone : Monotone wordMax := by
  intro w₁ w₂ hw
  simpa [wordMax] using Nat.sub_le_sub_right (wordBound_monotone hw) 1

/-- The maximum `w`-bit value is strictly below the exclusive bound `2^w`.

This is the basic relation between the inclusive maximum `wordMax w` and the
exclusive cap `wordBound w`, and later proofs use it to move from a
`≤ wordMax w` safety bound to a `< wordBound w` result. The proof unfolds
`wordMax` as `wordBound w - 1` and finishes by arithmetic. -/
theorem wordMax_lt_wordBound (w : Nat) : wordMax w < wordBound w := by
  have hbound : 0 < wordBound w := wordBound_pos w
  unfold wordMax
  omega

/-- The decoder lower bound is monotone in the word width.

This theorem is the key arithmetic fact behind width lifting: if a modulus has a
valid decoder window at width `w₁`, then the same modulus still has one at any
larger width `w₂`. The proof expands `decoderLowerBound`, observes that
`wordMax` is monotone by `wordMax_monotone`, and then pushes that monotonicity
through the two divisions and the final multiplication by `256`. -/
theorem decoderLowerBound_monotone (m : Nat) : Monotone fun w => decoderLowerBound w m := by
  intro w₁ w₂ hw
  unfold decoderLowerBound
  apply Nat.mul_le_mul_right
  exact Nat.div_le_div_right <| Nat.div_le_div_right (wordMax_monotone hw)

namespace SupportedModulus

/-- A modulus supported at width `w₁` is also supported at any larger width
`w₂`.

This is the bundled form of width monotonicity used by the examples and later
instantiations for `128`, `256`, and beyond. The proof preserves the radix
assumption `m ≥ 2` unchanged and lifts the decoder-window bound via
`decoderLowerBound_monotone`. -/
theorem of_width_le {w₁ w₂ m : Nat} (hw : w₁ ≤ w₂) :
    SupportedModulus w₁ m → SupportedModulus w₂ m := by
  intro hm
  exact ⟨hm.1, le_trans hm.2 <| decoderLowerBound_monotone m hw⟩

end SupportedModulus

/-- Existence of a fixed-width prefix length for modulus `m` and width `w`. We
prove this before defining `lengthPrefixDigits` so that the width can be chosen
by `Nat.find`. -/
lemma exists_power_ge_wordBound (w m : Nat) (hm : 2 ≤ m) :
    ∃ k, wordBound w ≤ m ^ k := by
  refine ⟨w, ?_⟩
  have hpow : ∀ k : Nat, 2 ^ k ≤ m ^ k := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul ih hm
  simpa [wordBound] using hpow w

/-- The minimal fixed prefix width needed to encode every `w`-bit value in base
`m`. Later files use this width for both the length prefix and the initial state
prefix. -/
def lengthPrefixDigits (w m : Nat) (hm : 2 ≤ m) : Nat :=
  Nat.find (exists_power_ge_wordBound w m hm)

/-- The chosen prefix width is large enough to represent any value below
`2^w`. This is the forward bound needed by the prefix encoder/decoder proofs. -/
theorem lengthPrefixDigits_spec (w m : Nat) (hm : 2 ≤ m) :
    wordBound w ≤ m ^ lengthPrefixDigits w m hm := by
  exact Nat.find_spec (exists_power_ge_wordBound w m hm)

/-- The chosen prefix width is minimal: any smaller width fails to cover all
`w`-bit values. This is used to justify that `lengthPrefixDigits` is not merely
some working width, but the least one. -/
theorem lengthPrefixDigits_minimal (w m : Nat) (hm : 2 ≤ m) {j : Nat}
    (hj : j < lengthPrefixDigits w m hm) :
      wordBound w > m ^ j := by
  simpa [wordBound] using Nat.find_min (exists_power_ge_wordBound w m hm) hj

/-- Projection of the first component of `SupportedModulus`. We isolate it
because later proofs repeatedly need the radix assumption `m ≥ 2`. -/
theorem modulus_ge_two {w m : Nat} (hm : SupportedModulus w m) : 2 ≤ m :=
  hm.1

/-- Projection of the second component of `SupportedModulus`. This is what later
proofs use to show that the normalization window can absorb one byte step. -/
theorem decoderLowerBound_ge_256 {w m : Nat} (hm : SupportedModulus w m) :
    256 ≤ decoderLowerBound w m :=
  hm.2

/-- A positive modulus extracted from `SupportedModulus`. This lemma exists so
later arithmetic proofs can use division and remainder lemmas that require
strict positivity. -/
theorem modulus_pos {w m : Nat} (hm : SupportedModulus w m) : 0 < m := by
  have htwo : 0 < (2 : Nat) := by decide
  exact lt_of_lt_of_le htwo hm.1

/-- Unfolding lemma for `decoderLowerBound`. It rewrites away the final
alignment-by-`256`, making algebra with `encoderThreshold` easier. -/
theorem decoderLowerBound_div_256 (w m : Nat) :
    decoderLowerBound w m / 256 = (wordMax w / m) / 256 := by
  unfold decoderLowerBound
  have h := Nat.mul_div_right ((wordMax w / m) / 256) (by decide : 0 < 256)
  simp at h ⊢

/-- The encoder threshold itself still fits below the word cap. This fact is
needed when proving that renormalized states never leave the bounded word
model. -/
theorem encoderThreshold_le_wordMax {w m : Nat} (_hm : SupportedModulus w m) :
    encoderThreshold w m ≤ wordMax w := by
  rw [encoderThreshold, decoderLowerBound_div_256]
  calc
    ((wordMax w / m) / 256) * m ≤ (wordMax w / m) * m := by
      exact Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ ≤ wordMax w := Nat.div_mul_le_self _ _

/-- Bundled parameters for the base-`m` transducer. The purpose of this
structure is to package a word width and a modulus together with the proof that
they satisfy the normalization side conditions. -/
structure Params where
  /-- Bit width used for fixed-width header values and state bounds. -/
  width : Nat
  /-- Base used for emitted digits and fixed-width prefixes. -/
  modulus : Nat
  /-- Proof that `modulus` admits a valid byte-aligned normalization window. -/
  supported : SupportedModulus width modulus

/-! The declarations above are the foundational theorems on a raw word width
`w` and modulus `m`. They appear before this namespace because `Params` is only
introduced afterward. The purpose of `namespace Params` is to re-express those
same facts for a bundled parameter package `p : Params`, so later files can
write concise statements about the system without carrying separate assumptions
by hand. -/
namespace Params

/-- The minimal fixed prefix width needed to encode every bounded word value in
base `m`. -/
def lengthPrefixDigits (p : Params) : Nat :=
  EncodingProofs.BaseMLen.lengthPrefixDigits p.width p.modulus (modulus_ge_two p.supported)

/-- Lower edge `L` of the normalized decoder state window for the byte-wise
transducer. It is the largest multiple of `256` such that `L * m ≤ wordMax
p.width`, which is exactly why later byte updates can stay inside the bounded
state space. -/
def decoderLowerBound (p : Params) : Nat :=
  EncodingProofs.BaseMLen.decoderLowerBound p.width p.modulus

/-- Encoder renormalization threshold `T`. Before absorbing a byte, the encoder
emits base-`m` digits until the state is below `T`; then the byte update
`x <- 256 * x + b` stays within the normalized window. -/
def encoderThreshold (p : Params) : Nat :=
  EncodingProofs.BaseMLen.encoderThreshold p.width p.modulus

/-- Projection of the first component of `SupportedModulus`. -/
theorem modulus_ge_two (p : Params) : 2 ≤ p.modulus :=
  EncodingProofs.BaseMLen.modulus_ge_two p.supported

/-- A positive modulus extracted from `SupportedModulus`. -/
theorem modulus_pos (p : Params) : 0 < p.modulus :=
  EncodingProofs.BaseMLen.modulus_pos p.supported

/-- Projection of the second component of `SupportedModulus`. -/
theorem decoderLowerBound_ge_256 (p : Params) : 256 ≤ p.decoderLowerBound :=
  EncodingProofs.BaseMLen.decoderLowerBound_ge_256 p.supported

/-- The encoder threshold itself still fits below the global word cap. This fact
is needed when proving that renormalized states never leave the bounded word
model. -/
theorem encoderThreshold_le_wordMax (p : Params) : p.encoderThreshold ≤ wordMax p.width :=
  EncodingProofs.BaseMLen.encoderThreshold_le_wordMax p.supported

/-- Positivity of the encoder threshold. This theorem exists for a concrete
reason: it is what lets the recursive termination proof for `renormEncode`
exclude the degenerate zero-threshold case. -/
theorem encoderThreshold_pos (p : Params) : 0 < p.encoderThreshold := by
  unfold Params.encoderThreshold EncodingProofs.BaseMLen.encoderThreshold
  have hdiv : 0 < p.decoderLowerBound / 256 := by
    exact Nat.div_pos p.decoderLowerBound_ge_256 (by decide)
  exact Nat.mul_pos hdiv p.modulus_pos

/-- Bundled version of `lengthPrefixDigits_spec`. It is used by the prefix
encoding/decoding proofs to show that `p.lengthPrefixDigits` covers all bounded
prefix values. -/
theorem lengthPrefixDigits_spec (p : Params) :
    wordBound p.width ≤ p.modulus ^ p.lengthPrefixDigits := by
  exact EncodingProofs.BaseMLen.lengthPrefixDigits_spec p.width p.modulus p.modulus_ge_two

/-- Bundled minimality of the chosen prefix width. This is used when later
proofs need the exact least-width characterization rather than only existence. -/
theorem lengthPrefixDigits_minimal (p : Params) {j : Nat} (hj : j < p.lengthPrefixDigits) :
    p.modulus ^ j < wordBound p.width := by
  exact EncodingProofs.BaseMLen.lengthPrefixDigits_minimal p.width p.modulus p.modulus_ge_two hj

end Params

end EncodingProofs.BaseMLen

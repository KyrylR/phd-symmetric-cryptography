import Mathlib

/-!
Core parameters for the length-delimited base-`m` byte encoder/decoder.

This file fixes the 64-bit state bound, defines the byte and digit types, chooses
the normalization constants `L` and `T`, and proves the arithmetic facts needed by
the later prefix, renormalization, and payload proofs.

The declarations are intentionally split into two layers:

* raw facts about a modulus `m`;
* bundled facts for `p : Params`, so later files do not have to repeat side
  conditions such as `SupportedModulus m`.
-/

namespace EncodingProofs.BaseMLen

/-- Exclusive upper bound on unsigned 64-bit values. We use this as the common
64-bit cap for prefix values, payload states, and encoded lengths. -/
def u64Bound : Nat := 2 ^ 64

/-- Largest unsigned 64-bit value. This is the top value allowed for states and
the quantity used to derive safe normalization bounds. -/
def u64Max : Nat := u64Bound - 1

/-- A byte, represented as a natural number in `[0, 256)`. We keep the type
explicit because the core development works on bytes rather than text. -/
abbrev Byte := Fin 256

/-- A base-`m` digit, represented as a natural number in `[0, m)`. This models
the residue symbols emitted by the encoder and consumed by the decoder. -/
abbrev Digit (m : Nat) := Fin m

/-- An unsigned 64-bit value, represented as a natural number in `[0, 2^64)`.
This is the type used for fixed-width prefix values after decoding. -/
abbrev U64Val := Fin u64Bound

/-- Lower edge `L` of the normalized decoder state window for the byte-wise
transducer. It is the largest multiple of `256` such that `L * m ≤ u64Max`,
which is exactly why later byte updates can stay inside the 64-bit state space. -/
def decoderLowerBound (m : Nat) : Nat := ((u64Max / m) / 256) * 256

/-- Encoder renormalization threshold `T`. Before absorbing a byte, the encoder
emits base-`m` digits until the state is below `T`; then the byte update
`x <- 256 * x + b` stays within the normalized window. -/
def encoderThreshold (m : Nat) : Nat := (decoderLowerBound m / 256) * m

/-- Supported moduli for the byte-wise transducer. We require `m ≥ 2` and
`decoderLowerBound m ≥ 256`, so the normalization window is nontrivial and
compatible with one-byte updates. This predicate formalizes the paper's phrase
"moduli for which the transducer parameters can be instantiated." -/
def SupportedModulus (m : Nat) : Prop := 2 ≤ m ∧ 256 ≤ decoderLowerBound m

/-- Existence of a fixed-width prefix length for modulus `m`. We prove this
before defining `lengthPrefixDigits` so that the width can be chosen by
`Nat.find`. -/
lemma exists_power_ge_u64Bound (m : Nat) (hm : 2 ≤ m) : ∃ k, u64Bound ≤ m ^ k := by
  apply Exists.intro 64
  have hpow : ∀ k : Nat, 2 ^ k ≤ m ^ k := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k ih =>
        simpa using
           Nat.mul_le_mul ih hm
  have hpow : 2 ^ 64 ≤ m ^ 64 := by
    exact hpow 64
  simpa [u64Bound] using hpow

/-- The minimal fixed prefix width needed to encode every 64-bit value in base
`m`. Later files use this width for both the length prefix and the initial state
prefix. -/
def lengthPrefixDigits (m : Nat) (hm : 2 ≤ m) : Nat :=
  Nat.find (exists_power_ge_u64Bound m hm)

/-- The chosen prefix width is large enough to represent any value below
`2^64`. This is the forward bound needed by the prefix encoder/decoder proofs. -/
theorem lengthPrefixDigits_spec (m : Nat) (hm : 2 ≤ m) :
    u64Bound ≤ m ^ lengthPrefixDigits m hm := by
  exact Nat.find_spec (exists_power_ge_u64Bound m hm)

/-- The chosen prefix width is minimal: any smaller width fails to cover all
64-bit values. This is used to justify that `lengthPrefixDigits` is not merely
some working width, but the least one. -/
theorem lengthPrefixDigits_minimal (m : Nat) (hm : 2 ≤ m) {j : Nat}
    (hj : j < lengthPrefixDigits m hm) :
      u64Bound > m ^ j := by
  simpa [u64Bound] using Nat.find_min (exists_power_ge_u64Bound m hm) hj

/-- Projection of the first component of `SupportedModulus`. We isolate it
because later proofs repeatedly need the radix assumption `m ≥ 2`. -/
theorem modulus_ge_two {m : Nat} (hm : SupportedModulus m) : 2 ≤ m :=
  hm.1

/-- Projection of the second component of `SupportedModulus`. This is what later
proofs use to show that the normalization window can absorb one byte step. -/
theorem decoderLowerBound_ge_256 {m : Nat} (hm : SupportedModulus m) :
    256 ≤ decoderLowerBound m :=
  hm.2

/-- A positive modulus extracted from `SupportedModulus`. This lemma exists so
later arithmetic proofs can use division and remainder lemmas that require
strict positivity. -/
theorem modulus_pos {m : Nat} (hm : SupportedModulus m) : 0 < m := by
  have htwo : 0 < (2 : Nat) := by decide
  exact lt_of_lt_of_le htwo hm.1

/-- Unfolding lemma for `decoderLowerBound`. It rewrites away the final
alignment-by-`256`, making algebra with `encoderThreshold` easier. -/
theorem decoderLowerBound_div_256 (m : Nat) :
    decoderLowerBound m / 256 = (u64Max / m) / 256 := by
  unfold decoderLowerBound
  have h := Nat.mul_div_right ((u64Max / m) / 256) (by decide : 0 < 256)
  simp at h ⊢

/-- The encoder threshold itself still fits below the 64-bit cap. This fact is
needed when proving that renormalized states never leave the `u64` model. -/
theorem encoderThreshold_le_u64Max {m : Nat} (hm : SupportedModulus m) :
    encoderThreshold m ≤ u64Max := by
  have hmpos := modulus_pos hm
  rw [encoderThreshold, decoderLowerBound_div_256]
  calc
    ((u64Max / m) / 256) * m ≤ (u64Max / m) * m := by
      exact Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    _ ≤ u64Max := Nat.div_mul_le_self _ _

/-- Bundled parameters for the base-`m` transducer. The purpose of this
structure is to package a modulus together with the proof that it satisfies the
64-bit normalization side conditions. -/
structure Params where
  /-- Base used for emitted digits and fixed-width prefixes. -/
  modulus : Nat
  /-- Proof that `modulus` admits a valid byte-aligned normalization window. -/
  supported : SupportedModulus modulus

/-! The declarations above are the foundational theorems on a raw modulus `m`.
They appear before this namespace because `Params` is only introduced afterward.
The purpose of `namespace Params` is to re-express those same facts for a bundled
parameter package `p : Params`, so later files can write concise statements about
the system without carrying separate assumptions by hand. -/
namespace Params

/-- The minimal fixed prefix width needed to encode every 64-bit value in base
`m`. Later files use this width for both the length prefix and the initial state
prefix. -/
def lengthPrefixDigits (p : Params) : Nat :=
  EncodingProofs.BaseMLen.lengthPrefixDigits p.modulus (modulus_ge_two p.supported)

/-- Lower edge `L` of the normalized decoder state window for the byte-wise
transducer. It is the largest multiple of `256` such that `L * m ≤ u64Max`,
which is exactly why later byte updates can stay inside the 64-bit state space. -/
def decoderLowerBound (p : Params) : Nat :=
  EncodingProofs.BaseMLen.decoderLowerBound p.modulus

/-- Encoder renormalization threshold `T`. Before absorbing a byte, the encoder
emits base-`m` digits until the state is below `T`; then the byte update
`x <- 256 * x + b` stays within the normalized window. -/
def encoderThreshold (p : Params) : Nat :=
  EncodingProofs.BaseMLen.encoderThreshold p.modulus

/-- Projection of the first component of `SupportedModulus`. We isolate it
because later proofs repeatedly need the radix assumption `m ≥ 2`. -/
theorem modulus_ge_two (p : Params) : 2 ≤ p.modulus :=
  EncodingProofs.BaseMLen.modulus_ge_two p.supported

/-- A positive modulus extracted from `SupportedModulus`. This lemma exists so
later arithmetic proofs can use division and remainder lemmas that require
strict positivity. -/
theorem modulus_pos (p : Params) : 0 < p.modulus :=
  EncodingProofs.BaseMLen.modulus_pos p.supported

/-- Projection of the second component of `SupportedModulus`. This is what later
proofs use to show that the normalization window can absorb one byte step. -/
theorem decoderLowerBound_ge_256 (p : Params) : 256 ≤ p.decoderLowerBound :=
  EncodingProofs.BaseMLen.decoderLowerBound_ge_256 p.supported

/-- The encoder threshold itself still fits below the 64-bit cap. This fact is
needed when proving that renormalized states never leave the `u64` model. -/
theorem encoderThreshold_le_u64Max (p : Params) : p.encoderThreshold ≤ u64Max :=
  EncodingProofs.BaseMLen.encoderThreshold_le_u64Max p.supported

/-- Positivity of the encoder threshold. This theorem exists for a concrete
reason: it is what lets the recursive termination proof for `renormEncode`
exclude the degenerate zero-threshold case. -/
theorem encoderThreshold_pos (p : Params) : 0 < p.encoderThreshold := by
  unfold Params.encoderThreshold EncodingProofs.BaseMLen.encoderThreshold
  have hdiv : 0 < p.decoderLowerBound / 256 := by
    exact Nat.div_pos p.decoderLowerBound_ge_256 (by decide)
  exact Nat.mul_pos hdiv p.modulus_pos

/-- Bundled version of `lengthPrefixDigits_spec`. It is used by the prefix
encoding/decoding proofs to show that `p.lengthPrefixDigits` covers all 64-bit
prefix values. -/
theorem lengthPrefixDigits_spec (p : Params) :
    u64Bound ≤ p.modulus ^ p.lengthPrefixDigits := by
  exact EncodingProofs.BaseMLen.lengthPrefixDigits_spec p.modulus p.modulus_ge_two

/-- Bundled minimality of the chosen prefix width. This is used when later proofs
need the exact least-width characterization rather than only existence. -/
theorem lengthPrefixDigits_minimal (p : Params) {j : Nat} (hj : j < p.lengthPrefixDigits) :
    p.modulus ^ j < u64Bound := by
  exact EncodingProofs.BaseMLen.lengthPrefixDigits_minimal p.modulus p.modulus_ge_two hj

end Params

end EncodingProofs.BaseMLen

import EncodingProofs.BaseMLen.Spec
import Mathlib

/-!
Prefix-correctness lemmas for the width-parametric length-delimited base-`m`
specification.

This file proves that fixed-width base-`m` prefixes have the expected shape and
that decoding reverses encoding on every value that fits into the chosen width.
These results are the bridge from the raw digit-level functions in `Spec` to the
header-level correctness statements used by the stream proofs.
-/

namespace EncodingProofs.BaseMLen

namespace Params

/-- Fixed-width prefix encoding really is fixed-width: encoding with width `k`
always produces exactly `k` digits. This theorem is needed by `decodePrefix?`,
which first checks the prefix length before decoding. The proof is a direct
induction on `k`. -/
theorem encodeFixedWidthNat_length (p : Params) (k value : Nat) :
    (encodeFixedWidthNat p k value).length = k := by
  induction k generalizing value with
  | zero =>
      simp [encodeFixedWidthNat]
  | succ k ih =>
      simp [encodeFixedWidthNat, ih]

/-- Decoding a fixed-width base-`m` encoding recovers the original value whenever
the value fits below `m^k`. This is the core prefix-inversion theorem.

How the proof works:

* base case `k = 0`: the assumption `value < m^0 = 1` forces `value = 0`;
* inductive step: from `value < m^(k+1) = m^k * m`, infer
  `value / m < m^k`, apply the induction hypothesis to the quotient, and then
  reconstruct `value` using the Euclidean division identity
  `value = value % m + m * (value / m)`.
-/
theorem decodeDigitsNat_encodeFixedWidthNat_of_lt (p : Params) :
    ∀ {k value : Nat},
      value < p.modulus ^ k →
      decodeDigitsNat p (encodeFixedWidthNat p k value) = value
  | 0, value, hlt => by
      have hlt1 : value < 1 := by
        simpa using hlt
      have hzero : value = 0 := by
        omega
      simp [encodeFixedWidthNat, decodeDigitsNat, hzero]
  | k + 1, value, hlt => by
      have hmul : value < p.modulus ^ k * p.modulus := by
        simpa [pow_succ] using hlt
      have hdiv : value / p.modulus < p.modulus ^ k := by
        exact (Nat.div_lt_iff_lt_mul p.modulus_pos).2 hmul
      calc
        decodeDigitsNat p (encodeFixedWidthNat p (k + 1) value)
            = value % p.modulus + p.modulus * decodeDigitsNat p (encodeFixedWidthNat p k (value / p.modulus)) := by
                simp [encodeFixedWidthNat, decodeDigitsNat, Params.natDigit]
        _ = value % p.modulus + p.modulus * (value / p.modulus) := by
              rw [decodeDigitsNat_encodeFixedWidthNat_of_lt p hdiv]
        _ = value := by
              simpa [Nat.mul_comm] using (Nat.mod_add_div value p.modulus)

/-- The fixed-width prefix decoder inverts `encodeFixedWidthNat` at the width
chosen by `p.lengthPrefixDigits`, provided the input value is below `2^w`.

How the proof works:

* `lengthPrefixDigits_spec` upgrades `value < 2^w` to
  `value < p.modulus ^ p.lengthPrefixDigits`;
* `encodeFixedWidthNat_length` discharges the decoder's width check;
* `decodeDigitsNat_encodeFixedWidthNat_of_lt` supplies the actual arithmetic
  inversion.
-/
theorem decodePrefix?_encodeFixedWidthNat (p : Params) {value : Nat}
    (hvalue : value < wordBound p.width) :
    decodePrefix? p (encodeFixedWidthNat p p.lengthPrefixDigits value) = some ⟨value, hvalue⟩ := by
  have hpow : value < p.modulus ^ p.lengthPrefixDigits :=
    lt_of_lt_of_le hvalue p.lengthPrefixDigits_spec
  simp [decodePrefix?, encodeFixedWidthNat_length, hvalue,
    decodeDigitsNat_encodeFixedWidthNat_of_lt p hpow]

/-- Specialization of `decodePrefix?_encodeFixedWidthNat` to the bounded type
`WordVal p.width`. This is the form used later when the header values are
already packaged with their proof of lying below `2^w`. -/
theorem decodePrefix?_encodePrefix (p : Params) (value : WordVal p.width) :
    decodePrefix? p (encodePrefix p value) = some value := by
  simpa [encodePrefix] using decodePrefix?_encodeFixedWidthNat p value.2

end Params

end EncodingProofs.BaseMLen

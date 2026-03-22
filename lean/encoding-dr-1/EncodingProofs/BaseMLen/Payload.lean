import EncodingProofs.BaseMLen.Renorm
import Mathlib

/-!
Payload-correctness lemmas for the length-delimited base-`m` specification.

This file proves that the streaming payload encoder keeps its state inside the
normalization window and that the payload decoder exactly inverts it, even in the
presence of an arbitrary trailing suffix. These results are later combined with
the fixed-width header lemmas to obtain full stream-level correctness.
-/

namespace EncodingProofs.BaseMLen

namespace Params

/-- The state returned by `encodePayload` always lies in the decoder window
`[L, L * m)`.

How the proof works: induct on the byte list. For the empty list, the state is
exactly `L`. For `b :: bs`, let `q = (renormEncode p tailState).1`. The lower
bound follows from `L / 256 ≤ q`, hence
`L = (L / 256) * 256 ≤ q * 256 ≤ q * 256 + b`. The upper bound follows from
`q < T`, hence `q * 256 + b < (q + 1) * 256 ≤ T * 256 = L * m`, using `b < 256`
and `encoderThreshold_mul_256`. This invariant is the core safety fact for the
streaming payload state machine. -/
theorem encodePayload_state_bounds (p : Params) :
    ∀ bs : List Byte,
      p.decoderLowerBound ≤ (encodePayload p bs).1 ∧
        (encodePayload p bs).1 < p.decoderLowerBound * p.modulus := by
  intro bs
  induction bs with
  | nil =>
      constructor
      · simp [encodePayload]
      · have hpos : 0 < p.decoderLowerBound := lt_of_lt_of_le (by decide : 0 < 256) p.decoderLowerBound_ge_256
        have hmod : 1 < p.modulus := lt_of_lt_of_le (by decide : 1 < 2) p.modulus_ge_two
        simpa [encodePayload] using
          (Nat.mul_lt_mul_of_pos_left hmod hpos : p.decoderLowerBound * 1 < p.decoderLowerBound * p.modulus)
  | cons b bs ih =>
      let tail := encodePayload p bs
      let q := (renormEncode p tail.1).1
      have htail := ih
      have hchunk :
          p.decoderLowerBound / 256 ≤ q := by
        exact renormEncode_fst_ge_chunk p tail.1 <| le_trans (Nat.div_le_self _ _) htail.1
      have hq : q < p.encoderThreshold := by
        exact renormEncode_fst_lt_threshold p tail.1
      constructor
      · have hmul : (p.decoderLowerBound / 256) * 256 ≤ q * 256 := by
          exact Nat.mul_le_mul_right 256 hchunk
        have hbound : p.decoderLowerBound ≤ q * 256 := by
          simpa [p.decoderLowerBound_div_mul_256, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
        exact le_trans hbound (Nat.le_add_right _ _)
      · have hlt1 : q * 256 + b.1 < (q + 1) * 256 := by
          have hb : b.1 < 256 := b.2
          have hb' : q * 256 + b.1 < q * 256 + 256 := Nat.add_lt_add_left hb (q * 256)
          have hEq : q * 256 + 256 = (q + 1) * 256 := by
            ring
          exact lt_of_lt_of_eq hb' hEq
        have hlt2 : (q + 1) * 256 ≤ p.encoderThreshold * 256 := by
          exact Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt hq)
        exact lt_of_lt_of_le hlt1 <| by
          simpa [tail, q, encodePayload, p.encoderThreshold_mul_256] using hlt2

/-- The payload state also lies below the global 64-bit bound `2^64`.

How the proof works: combine `encodePayload_state_bounds`, which gives
`state < L * m`, with `decoderLowerBound_mul_modulus_le_u64Max` and the trivial
fact `u64Max < u64Bound`. This theorem is used when the payload state is later
stored in the fixed-width state prefix. -/
theorem encodePayload_state_lt_u64Bound (p : Params) (bs : List Byte) :
    (encodePayload p bs).1 < u64Bound := by
  have hbound := (encodePayload_state_bounds p bs).2
  have hu64 : p.decoderLowerBound * p.modulus ≤ u64Max := p.decoderLowerBound_mul_modulus_le_u64Max
  have humax : u64Max < u64Bound := by
    simp [u64Max, u64Bound]
  exact lt_of_lt_of_le hbound (le_trans hu64 (Nat.le_of_lt humax))

/-- Main payload roundtrip theorem with an arbitrary trailing suffix. Decoding
exactly `bs.length` bytes from the state/payload pair produced by `encodePayload`
recovers `bs` and leaves the extra suffix untouched.

How the proof works: induct on the byte list. For `b :: bs`, write the tail
payload as `(tailState, tailDigits)` and the renormalized state as
`ren = renormEncode p tailState`. The renormalization theorem
`renorm_roundtrip_with_suffix` restores `tailState` from `ren`, and the byte step
is inverted by the arithmetic equalities
`(ren.1 * 256 + b) % 256 = b` and `(ren.1 * 256 + b) / 256 = ren.1`. After those
two identities, the induction hypothesis finishes the tail. -/
theorem payload_roundtrip_with_suffix (p : Params) :
    ∀ (bs : List Byte) (rest : List (Digit p.modulus)),
      decodePayload p bs.length (encodePayload p bs).1 ((encodePayload p bs).2 ++ rest) = .ok (bs, rest)
  | [], rest => by
      simp [decodePayload, encodePayload]
  | b :: bs, rest => by
      let tail := encodePayload p bs
      let ren := renormEncode p tail.1
      have htailDecode := payload_roundtrip_with_suffix p bs rest
      have htailBounds := encodePayload_state_bounds p bs
      have hren :
          renormDecode p ren.1 (ren.2 ++ tail.2 ++ rest) = .ok (tail.1, tail.2 ++ rest) := by
        simpa [tail, ren, List.append_assoc] using
          renorm_roundtrip_with_suffix p htailBounds.1 htailBounds.2 (tail.2 ++ rest)
      have hren' :
          renormDecode p ren.1 (ren.2 ++ (tail.2 ++ rest)) = .ok (tail.1, tail.2 ++ rest) := by
        simpa [List.append_assoc] using hren
      have htailDecode' :
          decodePayload p bs.length tail.1 (tail.2 ++ rest) = .ok (bs, rest) := by
        simpa [tail] using htailDecode
      have hmod : (ren.1 * 256 + b.1) % 256 = b.1 := by
        simp [Nat.add_mod, Nat.mod_eq_of_lt b.2]
      have hdiv : (ren.1 * 256 + b.1) / 256 = ren.1 := by
        simpa [Nat.add_comm, Nat.div_eq_of_lt b.2] using
          (Nat.add_mul_div_right b.1 ren.1 (by decide : 0 < 256))
      simp [decodePayload, encodePayload, tail, ren, List.append_assoc, hmod, hdiv]
      rw [hren']
      simp
      rw [htailDecode']

/-- Alias of `payload_roundtrip_with_suffix` under a decode/encode-oriented name.
Later files use this form when they want the statement to read as a direct
inverse law. -/
theorem decodePayload_encodePayload_rest (p : Params) :
    ∀ (bs : List Byte) (rest : List (Digit p.modulus)),
      decodePayload p bs.length (encodePayload p bs).1 ((encodePayload p bs).2 ++ rest) = .ok (bs, rest) :=
  payload_roundtrip_with_suffix p

/-- Empty-suffix specialization of `payload_roundtrip_with_suffix`. This is the
closed payload roundtrip statement with no extra trailing digits. -/
theorem payload_roundtrip (p : Params) :
    ∀ bs : List Byte,
      decodePayload p bs.length (encodePayload p bs).1 (encodePayload p bs).2 = .ok (bs, [])
  | bs => by
      simpa using payload_roundtrip_with_suffix p bs []

/-- Alias of `payload_roundtrip` under the decode/encode-oriented name used by
the stream layer. -/
theorem decodePayload_encodePayload (p : Params) :
    ∀ bs : List Byte,
      decodePayload p bs.length (encodePayload p bs).1 (encodePayload p bs).2 = .ok (bs, []) :=
  payload_roundtrip p

end Params

end EncodingProofs.BaseMLen

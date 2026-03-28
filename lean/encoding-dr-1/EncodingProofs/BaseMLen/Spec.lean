import EncodingProofs.BaseMLen.Params
import Mathlib

/-!
Executable specification of the width-parametric length-delimited base-`m` byte
encoder/decoder.

This file builds on `Params` by defining the concrete wire format, the prefix
and payload transformations, and small adapters used by the examples. The key
point is that everything below operates for a fixed supported parameter package
`p`, so the implementation can refer directly to `p.width`, `p.modulus`,
`p.lengthPrefixDigits`, `p.decoderLowerBound`, and `p.encoderThreshold`.
-/

namespace EncodingProofs.BaseMLen

/-- Byte strings accepted by the encoder. The length bound exists because the
wire format stores the byte length in a fixed-width `w`-bit prefix. -/
abbrev ByteString (w : Nat) := { bs : List Byte // bs.length < wordBound w }

/-- Errors reported by the decoder when the input stream is too short or violates
the format invariants. The constructors distinguish which stage of the wire
format parse failed. -/
inductive DecodeError where
  /-- The stream ended before the length prefix was fully read. -/
  | notEnoughLengthDigits
  /-- A fixed-width prefix decoded to a value outside `[0, 2^w)`. -/
  | decodedValueTooLarge
  /-- The stream ended before the state prefix was fully read. -/
  | notEnoughStateDigits
  /-- The decoded initial state was below `decoderLowerBound`. -/
  | invalidState
  /-- Decoder renormalization needed another payload digit, but none remained. -/
  | notEnoughPayloadDigits
  deriving DecidableEq, Repr

namespace Params

/-- Canonical base-`m` digit associated to `value`, obtained by reduction modulo
`m`. This exists because both prefix encoding and renormalization need a uniform
way to turn a natural number into one emitted residue in `[0, m)`. -/
def natDigit (p : Params) (value : Nat) : Digit p.modulus :=
  ⟨value % p.modulus, Nat.mod_lt _ p.modulus_pos⟩

/-- Encode `value` into exactly `k` little-endian base-`m` digits. This is used
for the fixed-width length and state prefixes. For example, with `m = 3` and
`k = 4`, `34` is encoded as `[1, 2, 0, 1]`. The function keeps exactly `k`
digits; later correctness proofs rely on separate bounds showing that the values
encoded here actually fit into that width. -/
def encodeFixedWidthNat (p : Params) : Nat → Nat → List (Digit p.modulus)
  | 0, _ => []
  | k + 1, value => p.natDigit value :: encodeFixedWidthNat p k (value / p.modulus)

/-- Encode a bounded word value using the fixed prefix width selected by `p`.
This is the common serializer used for both the byte length and the initial
decoder state in the wire format. -/
def encodePrefix (p : Params) (value : WordVal p.width) : List (Digit p.modulus) :=
  encodeFixedWidthNat p p.lengthPrefixDigits value.1

/-- Interpret a little-endian base-`m` digit list as a natural number. This is
the algebraic inverse direction paired with `encodeFixedWidthNat` and is used to
decode the length and state prefixes. For example, with `m = 3`, the list
`[1, 2, 0, 1]` evaluates to `34`. -/
def decodeDigitsNat (p : Params) : List (Digit p.modulus) → Nat
  | [] => 0
  | d :: ds => d.1 + p.modulus * decodeDigitsNat p ds

/-- Decode a fixed-width prefix back into a bounded word value. The length check
enforces that the caller supplied exactly one prefix block, and the final bound
check rejects values outside `[0, 2^w)`. -/
def decodePrefix? (p : Params) (digits : List (Digit p.modulus)) : Option (WordVal p.width) :=
  if _ : digits.length = p.lengthPrefixDigits then
    let value := decodeDigitsNat p digits
    if hval : value < wordBound p.width then
      some ⟨value, hval⟩
    else
      none
  else
    none

/-- Encoder-side renormalization. While the current state is at or above the
encoder threshold, emit one base-`m` digit and divide by `m` until the state is
small enough to absorb the next byte via `x <- 256 * x + b`. -/
def renormEncode (p : Params) (x : Nat) : Nat × List (Digit p.modulus) :=
  if h : p.encoderThreshold ≤ x then
    let _ := h
    let digit := p.natDigit x
    let rest := renormEncode p (x / p.modulus)
    (rest.1, rest.2 ++ [digit])
  else
    (x, [])
  termination_by x
  decreasing_by
    have hx : 0 < x := lt_of_lt_of_le p.encoderThreshold_pos h
    have hm : 1 < p.modulus := lt_of_lt_of_le (by decide : 1 < 2) p.modulus_ge_two
    exact Nat.div_lt_self hx hm

/-- Decoder-side renormalization. If the current state is below the decoder
lower bound, consume payload digits until the state returns to the working
window `[L, L * m)`. This is the inverse operational counterpart to
`renormEncode`. -/
def renormDecode (p : Params) (x : Nat) (digits : List (Digit p.modulus)) :
    Except DecodeError (Nat × List (Digit p.modulus)) :=
  if _h : p.decoderLowerBound ≤ x then
    .ok (x, digits)
  else
    match digits with
    | [] => .error .notEnoughPayloadDigits
    | d :: rest => renormDecode p (x * p.modulus + d.1) rest
  termination_by digits.length
  decreasing_by
    simp

/-- Encode the payload bytes into an rANS-style state/payload pair. The returned
state is the final normalized state stored in the fixed-width header, and the
returned digit list is the emitted payload suffix. This function is the core
streaming encoder for the byte data itself. -/
def encodePayload (p : Params) : List Byte → Nat × List (Digit p.modulus)
  | [] => (p.decoderLowerBound, [])
  | b :: bs =>
      let tail := encodePayload p bs
      let tailState := tail.1
      let tailDigits := tail.2
      let renorm := renormEncode p tailState
      let normalized := renorm.1
      let prefixDigits := renorm.2
      (normalized * 256 + b.1, prefixDigits ++ tailDigits)

/-- Decode `len` payload bytes from a starting state and payload suffix. Each
step recovers one byte by splitting the current state into `state % 256` and
`state / 256`, then uses `renormDecode` to restore the next working state. The
extra returned digit list makes trailing-padding tolerance explicit. -/
def decodePayload (p : Params) :
    Nat → Nat → List (Digit p.modulus) → Except DecodeError (List Byte × List (Digit p.modulus))
  | 0, _, payload => .ok ([], payload)
  | len + 1, state, payload =>
      let byte : Byte := ⟨state % 256, Nat.mod_lt _ (by decide)⟩
      let normalized := state / 256
      match renormDecode p normalized payload with
      | .error err => .error err
      | .ok (tailState, remaining) =>
          match decodePayload p len tailState remaining with
          | .error err => .error err
          | .ok (decoded, rest) => .ok (byte :: decoded, rest)

/-- Encode a byte string into the external wire format `length || state ||
payload`. The fixed-width prefixes carry the byte length and final state; the
payload digits are produced by `encodePayload`. -/
def encode (p : Params) (bytes : ByteString p.width) : List (Digit p.modulus) :=
  let lenDigits := encodeFixedWidthNat p p.lengthPrefixDigits bytes.1.length
  let (state, payload) := encodePayload p bytes.1
  let stateDigits := encodeFixedWidthNat p p.lengthPrefixDigits state
  lenDigits ++ stateDigits ++ payload

/-- Decode a wire-format stream `length || state || payload` back into the
original bytes. The function validates the header structure, checks the decoded
state invariant, and ignores any trailing suffix left after the declared payload
has been recovered. -/
def decode (p : Params) (digits : List (Digit p.modulus)) : Except DecodeError (List Byte) :=
  let k := p.lengthPrefixDigits
  if _ : digits.length < k then
    .error .notEnoughLengthDigits
  else
    let lenDigits := digits.take k
    match p.decodePrefix? lenDigits with
    | none => .error .decodedValueTooLarge
    | some lenVal =>
        if _ : lenVal.1 = 0 then
          .ok []
        else if _ : (digits.drop k).length < k then
          .error .notEnoughStateDigits
        else
          let stateDigits := (digits.drop k).take k
          match p.decodePrefix? stateDigits with
          | none => .error .decodedValueTooLarge
          | some stateVal =>
              if _ : stateVal.1 < p.decoderLowerBound then
                .error .invalidState
              else
                match p.decodePayload lenVal.1 stateVal.1 (digits.drop (2 * k)) with
                | .error err => .error err
                | .ok (decoded, _) => .ok decoded

/-- Convert a natural number to a byte if it lies in `[0, 256)`. This adapter
exists for tests and examples that are easier to write using `Nat`. -/
def byteOfNat? (n : Nat) : Option Byte :=
  if h : n < 256 then
    some ⟨n, h⟩
  else
    none

/-- Convert a natural number to a base-`m` digit if it lies in `[0, m)`. This is
the digit analogue of `byteOfNat?`, again used by examples and test helpers. -/
def digitOfNat? (p : Params) (n : Nat) : Option (Digit p.modulus) :=
  if h : n < p.modulus then
    some ⟨n, h⟩
  else
    none

/-- Validate an entire list of naturals as bytes. The purpose of this helper is
to let examples feed ordinary numeric lists into the specification layer. -/
def bytesOfNatList? : List Nat → Option (List Byte)
  | [] => some []
  | n :: ns =>
      match byteOfNat? n, bytesOfNatList? ns with
      | some b, some bs => some (b :: bs)
      | _, _ => none

/-- Validate an entire list of naturals as base-`m` digits. This mirrors
`bytesOfNatList?` for encoded streams written as plain naturals. -/
def digitsOfNatList? (p : Params) : List Nat → Option (List (Digit p.modulus))
  | [] => some []
  | n :: ns =>
      match digitOfNat? p n, digitsOfNatList? p ns with
      | some d, some ds => some (d :: ds)
      | _, _ => none

/-- Convenience wrapper around `encode` for `List Nat` inputs. It first validates
that the input list really consists of bytes and satisfies the global length
bound, then returns the encoded digits as plain naturals. -/
def encodeNatBytes? (p : Params) (bytes : List Nat) : Option (List Nat) :=
  match bytesOfNatList? bytes with
  | none => none
  | some bs =>
      if h : bs.length < wordBound p.width then
        some <| (encode p ⟨bs, h⟩).map Fin.val
      else
        none

/-- Convenience wrapper around `decode` for streams written as `List Nat`. It
first validates the digits against the modulus, then erases the byte proofs in
the successful output. -/
def decodeNatDigits? (p : Params) (digits : List Nat) : Option (List Nat) :=
  match digitsOfNatList? p digits with
  | none => none
  | some ds =>
      match decode p ds with
      | .error _ => none
      | .ok bytes => some (bytes.map Fin.val)

end Params

end EncodingProofs.BaseMLen

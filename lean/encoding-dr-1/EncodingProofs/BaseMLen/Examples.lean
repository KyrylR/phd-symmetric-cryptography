import EncodingProofs.BaseMLen.Stream

namespace EncodingProofs.BaseMLen

def params25 : Params where
  modulus := 25
  supported := by
    unfold SupportedModulus decoderLowerBound u64Max u64Bound
    native_decide

def params50 : Params where
  modulus := 50
  supported := by
    unfold SupportedModulus decoderLowerBound u64Max u64Bound
    native_decide

def params257 : Params where
  modulus := 257
  supported := by
    unfold SupportedModulus decoderLowerBound u64Max u64Bound
    native_decide

def sampleBytes : List Nat := [72, 105]

def encodeNatList? (p : Params) (bytes : List Nat) : Option (List Nat) :=
  p.encodeNatBytes? bytes

def decodeNatList? (p : Params) (bytes : List Nat) : Option (List Nat) :=
  p.decodeNatDigits? bytes

def roundTripNatList? (p : Params) (bytes : List Nat) : Option (List Nat) := do
  let digits <- p.encodeNatBytes? bytes
  p.decodeNatDigits? digits

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 20, 10, 1, 7, 2, 15, 9, 21, 1, 23, 1, 2, 0, 23, 2]
-- Here `p.lengthPrefixDigits = 14` (min k such 2^64 < 25^k), so the output has the form
-- `length || state || payload`.
-- The first 14 digits are the fixed-width encoding of the byte length `2`,
-- the next 14 digits are the fixed-width encoding of the final state,
-- and the last 3 digits are the payload.
#eval encodeNatList? params25 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params25 sampleBytes

-- Expected: some [72, 105]
-- This list starts with a valid encoding of the message `[72, 105]` and then has
-- extra trailing digits appended. The decoder still recovers the original
-- message, because the stream-level theorem `stream_roundtrip_with_suffix`
-- shows that trailing suffix digits are ignored once the declared payload has
-- been decoded.
#eval decodeNatList? params25 [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 20, 10, 1, 7, 2, 15, 9, 21, 1, 23, 1, 2, 0, 23, 2, 0, 0, 0, 0, 0, 0, 6, 5, 4, 3, 2, 1]

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 8, 11, 36, 6, 32, 19, 0, 38, 1, 49, 1, 1, 48]
#eval encodeNatList? params50 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params50 sampleBytes

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 105, 141, 208, 5, 209, 137, 44, 247, 111]
#eval encodeNatList? params257 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params257 sampleBytes

end EncodingProofs.BaseMLen

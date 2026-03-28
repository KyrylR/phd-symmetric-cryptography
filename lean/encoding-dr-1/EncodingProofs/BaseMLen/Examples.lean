import EncodingProofs.BaseMLen.Stream

namespace EncodingProofs.BaseMLen

def params25_64 : Params where
  width := 64
  modulus := 25
  supported := by
    unfold SupportedModulus decoderLowerBound wordMax wordBound
    native_decide

def params50_64 : Params where
  width := 64
  modulus := 50
  supported := by
    unfold SupportedModulus decoderLowerBound wordMax wordBound
    native_decide

def params257_64 : Params where
  width := 64
  modulus := 257
  supported := by
    unfold SupportedModulus decoderLowerBound wordMax wordBound
    native_decide

def params25_128 : Params where
  width := 128
  modulus := 25
  supported := SupportedModulus.of_width_le (by decide) params25_64.supported

def params25_256 : Params where
  width := 256
  modulus := 25
  supported := SupportedModulus.of_width_le (by decide) params25_64.supported

def params50_128 : Params where
  width := 128
  modulus := 50
  supported := SupportedModulus.of_width_le (by decide) params50_64.supported

def params257_256 : Params where
  width := 256
  modulus := 257
  supported := SupportedModulus.of_width_le (by decide) params257_64.supported

def sampleBytes : List Nat := [72, 105]

def encodeNatList? (p : Params) (bytes : List Nat) : Option (List Nat) :=
  p.encodeNatBytes? bytes

def decodeNatList? (p : Params) (bytes : List Nat) : Option (List Nat) :=
  p.decodeNatDigits? bytes

def roundTripNatList? (p : Params) (bytes : List Nat) : Option (List Nat) := do
  let digits <- p.encodeNatBytes? bytes
  p.decodeNatDigits? digits

example : SupportedModulus 128 25 :=
  SupportedModulus.of_width_le (by decide) params25_64.supported

example : SupportedModulus 256 257 :=
  SupportedModulus.of_width_le (by decide) params257_64.supported

example (bytes : ByteString 128) :
    Params.decode params25_128 (Params.encode params25_128 bytes) = .ok bytes.1 := by
  simpa using Params.decode_encode params25_128 bytes

example (bytes : ByteString 256) :
    Params.decode params257_256 (Params.encode params257_256 bytes) = .ok bytes.1 := by
  simpa using Params.decode_encode params257_256 bytes

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 20, 10, 1, 7, 2, 15, 9, 21, 1, 23, 1, 2, 0, 23, 2]
-- Here `p.lengthPrefixDigits = 14` (min k such that `2^64 ≤ 25^k`), so the
-- output has the form `length || state || payload`.
-- The first 14 digits are the fixed-width encoding of the byte length `2`,
-- the next 14 digits are the fixed-width encoding of the final state,
-- and the last 3 digits are the payload.
#eval encodeNatList? params25_64 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params25_64 sampleBytes

-- Expected: some [72, 105]
-- This list starts with a valid encoding of the message `[72, 105]` and then
-- has extra trailing digits appended. The decoder still recovers the original
-- message, because the stream-level theorem `stream_roundtrip_with_suffix`
-- shows that trailing suffix digits are ignored once the declared payload has
-- been decoded.
#eval decodeNatList? params25_64 [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 20, 10, 1, 7, 2, 15, 9, 21, 1, 23, 1, 2, 0, 23, 2, 0, 0, 0, 0, 0, 0, 6, 5, 4, 3, 2, 1]

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 8, 11, 36, 6, 32, 19, 0, 38, 1, 49, 1, 1, 48]
#eval encodeNatList? params50_64 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params50_64 sampleBytes

-- Expected: some [2, 0, 0, 0, 0, 0, 0, 0, 105, 141, 208, 5, 209, 137, 44, 247, 111]
#eval encodeNatList? params257_64 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params257_64 sampleBytes

-- These width-lifted examples exercise the generic development at larger word
-- sizes while keeping the same byte sample.
-- Expected: some [72, 105]
#eval roundTripNatList? params25_128 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params25_256 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params50_128 sampleBytes
-- Expected: some [72, 105]
#eval roundTripNatList? params257_256 sampleBytes

end EncodingProofs.BaseMLen

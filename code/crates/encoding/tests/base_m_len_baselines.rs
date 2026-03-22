#[path = "support/base_m_len_support.rs"]
mod support;

use sym_adv_encoding::utf8::{Utf8Encoding, Utf8EncodingType};

#[test]
fn test_biguint_base_m_len_roundtrips_special_cases_and_random_payloads() {
    let cases = [
        Vec::new(),
        vec![0x00, 0x00, 0x01, 0x02, 0x00],
        support::random_bytes(31, 7),
        support::random_bytes(257, 19),
    ];

    for modulus in support::SHARED_COMPARISON_MODULI {
        for bytes in &cases {
            let encoded = support::encode_bytes_biguint_base_m_len(bytes, modulus)
                .expect("biguint baseline encode must succeed");
            let decoded = support::decode_bytes_biguint_base_m_len(&encoded, modulus)
                .expect("biguint baseline decode must succeed");
            assert_eq!(decoded, *bytes);
        }
    }
}

#[test]
fn test_biguint_and_native_baselines_decode_to_identical_bytes() {
    let cases = [
        Vec::new(),
        vec![0x00, 0x00, 0x01, 0x02, 0x00],
        support::random_bytes(64, 23),
        support::random_bytes(1536, 29),
    ];

    for modulus in support::SHARED_COMPARISON_MODULI {
        let native =
            Utf8Encoding::try_from(modulus, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .expect("native encoder construction must succeed");

        for bytes in &cases {
            let native_encoded = native
                .encode_bytes_base_m_len(bytes)
                .expect("native encode must succeed");
            let native_decoded = native
                .decode_bytes_base_m_len(&native_encoded)
                .expect("native decode must succeed");
            let bigint_encoded = support::encode_bytes_biguint_base_m_len(bytes, modulus)
                .expect("biguint baseline encode must succeed");
            let bigint_decoded = support::decode_bytes_biguint_base_m_len(&bigint_encoded, modulus)
                .expect("biguint baseline decode must succeed");

            assert_eq!(native_decoded, *bytes);
            assert_eq!(bigint_decoded, *bytes);
            assert_eq!(native_decoded, bigint_decoded);
        }
    }
}

#[test]
fn test_constriction_ans_reference_roundtrips_bytes() {
    let cases = [
        Vec::new(),
        vec![0x00, 0x00, 0x01, 0x02, 0x00],
        support::random_bytes(32, 31),
        support::random_bytes(2048, 37),
    ];

    for bytes in &cases {
        let encoded = support::encode_bytes_constriction_ans(bytes)
            .expect("ANS reference encode must succeed");
        let decoded = support::decode_bytes_constriction_ans(&encoded, bytes.len())
            .expect("ANS reference decode must succeed");
        assert_eq!(decoded, *bytes);
    }
}

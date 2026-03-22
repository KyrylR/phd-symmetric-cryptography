#[path = "../tests/support/base_m_len_support.rs"]
mod support;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use std::hint::black_box;
use sym_adv_encoding::utf8::{Utf8Encoding, Utf8EncodingType};

fn benchmark_native_encode_bytes(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("encode_bytes_base_m_len");

    for modulus in support::SHARED_COMPARISON_MODULI
        .into_iter()
        .chain([support::NATIVE_ONLY_MODULUS])
    {
        let encoding =
            Utf8Encoding::try_from(modulus, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .expect("native encoder construction must succeed");

        for (len, label) in support::BYTE_CASES {
            let bytes = support::random_bytes(len, 0xBEEF_u64 + len as u64);
            group.throughput(Throughput::Bytes(len as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("m{modulus}"), label),
                &bytes,
                |bencher, data| {
                    bencher.iter(|| {
                        let encoded = encoding
                            .encode_bytes_base_m_len(black_box(data))
                            .expect("native encode must succeed");
                        black_box(encoded);
                    });
                },
            );
        }
    }

    group.finish();
}

fn benchmark_native_decode_bytes(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("decode_bytes_base_m_len");

    for modulus in support::SHARED_COMPARISON_MODULI
        .into_iter()
        .chain([support::NATIVE_ONLY_MODULUS])
    {
        let encoding =
            Utf8Encoding::try_from(modulus, Utf8EncodingType::LengthDelimitedBaseMTransduction)
                .expect("native encoder construction must succeed");

        for (len, label) in support::BYTE_CASES {
            let bytes = support::random_bytes(len, 0xCAFE_u64 + len as u64);
            let encoded = encoding
                .encode_bytes_base_m_len(&bytes)
                .expect("native decode setup must succeed");

            group.throughput(Throughput::Bytes(len as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("m{modulus}"), label),
                &encoded,
                |bencher, digits| {
                    bencher.iter(|| {
                        let decoded = encoding
                            .decode_bytes_base_m_len(black_box(digits))
                            .expect("native decode must succeed");
                        black_box(decoded);
                    });
                },
            );
        }
    }

    group.finish();
}

fn benchmark_native_text_smoke(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("text_base_m_len_smoke");
    let encoding = Utf8Encoding::try_from(
        support::TEXT_SMOKE_MODULUS,
        Utf8EncodingType::LengthDelimitedBaseMTransduction,
    )
    .expect("native text encoder construction must succeed");

    for (len, label) in support::TEXT_CASES {
        let text = support::mixed_utf8_text(len);
        let encoded = encoding
            .encode_text_base_m_len(&text)
            .expect("text decode setup must succeed");

        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(
            BenchmarkId::new("encode_text_m65", label),
            &text,
            |bencher, data| {
                bencher.iter(|| {
                    let encoded = encoding
                        .encode_text_base_m_len(black_box(data))
                        .expect("text encode must succeed");
                    black_box(encoded);
                });
            },
        );

        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(
            BenchmarkId::new("decode_text_m65", label),
            &encoded,
            |bencher, digits| {
                bencher.iter(|| {
                    let decoded = encoding
                        .decode_text_base_m_len(black_box(digits))
                        .expect("text decode must succeed");
                    black_box(decoded);
                });
            },
        );
    }

    group.finish();
}

fn benchmark_biguint_exact_encode_bytes(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("biguint_exact_encode_bytes_base_m_len");

    for modulus in support::SHARED_COMPARISON_MODULI {
        for (len, label) in support::BYTE_CASES {
            let bytes = support::random_bytes(len, 0xFACE_u64 + len as u64);
            group.throughput(Throughput::Bytes(len as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("m{modulus}"), label),
                &bytes,
                |bencher, data| {
                    bencher.iter(|| {
                        let encoded =
                            support::encode_bytes_biguint_base_m_len(black_box(data), modulus)
                                .expect("biguint reference encode must succeed");
                        black_box(encoded);
                    });
                },
            );
        }
    }

    group.finish();
}

fn benchmark_biguint_exact_decode_bytes(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("biguint_exact_decode_bytes_base_m_len");

    for modulus in support::SHARED_COMPARISON_MODULI {
        for (len, label) in support::BYTE_CASES {
            let bytes = support::random_bytes(len, 0xABCD_u64 + len as u64);
            let encoded = support::encode_bytes_biguint_base_m_len(&bytes, modulus)
                .expect("biguint reference decode setup must succeed");

            group.throughput(Throughput::Bytes(len as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("m{modulus}"), label),
                &encoded,
                |bencher, digits| {
                    bencher.iter(|| {
                        let decoded =
                            support::decode_bytes_biguint_base_m_len(black_box(digits), modulus)
                                .expect("biguint reference decode must succeed");
                        black_box(decoded);
                    });
                },
            );
        }
    }

    group.finish();
}

fn benchmark_constriction_ans_reference_encode(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("constriction_ans_reference_encode_bytes");

    for (len, label) in support::BYTE_CASES {
        let bytes = support::random_bytes(len, 0x1357_u64 + len as u64);
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(label),
            &bytes,
            |bencher, data| {
                bencher.iter(|| {
                    let encoded = support::encode_bytes_constriction_ans(black_box(data))
                        .expect("ANS reference encode must succeed");
                    black_box(encoded);
                });
            },
        );
    }

    group.finish();
}

fn benchmark_constriction_ans_reference_decode(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("constriction_ans_reference_decode_bytes");

    for (len, label) in support::BYTE_CASES {
        let bytes = support::random_bytes(len, 0x2468_u64 + len as u64);
        let encoded = support::encode_bytes_constriction_ans(&bytes)
            .expect("ANS reference decode setup must succeed");

        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(label),
            &encoded,
            |bencher, words| {
                bencher.iter(|| {
                    let decoded = support::decode_bytes_constriction_ans(black_box(words), len)
                        .expect("ANS reference decode must succeed");
                    black_box(decoded);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    benchmark_native_encode_bytes,
    benchmark_native_decode_bytes,
    benchmark_native_text_smoke,
    benchmark_biguint_exact_encode_bytes,
    benchmark_biguint_exact_decode_bytes,
    benchmark_constriction_ans_reference_encode,
    benchmark_constriction_ans_reference_decode
);
criterion_main!(benches);

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use trendmarketv2::dec::{twap_update, PriceSample, TwapState};

fn build_samples() -> Vec<PriceSample> {
    (1..=600)
        .map(|i| PriceSample {
            timestamp_ms: (i * 1_000) as u64,
            price: 100.0 + (i as f64).sin() * 1.5 + (i % 7) as f64 * 0.02,
        })
        .collect()
}

fn bench_twap_update(c: &mut Criterion) {
    let samples = build_samples();
    c.bench_function("twap_update", |b| {
        b.iter_batched(
            || TwapState::new(Duration::from_secs(300), 100.0, 0),
            |mut state| {
                for sample in &samples {
                    let twap = twap_update(&mut state, *sample);
                    black_box(twap);
                }
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench_twap_update);
criterion_main!(benches);

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use trendmarketv2::dec::{match_core, OrderBook, OrderLevel, Side};

fn build_order_book() -> (OrderBook, OrderLevel) {
    let bids = (0..64)
        .map(|i| {
            let price = 100.0 - f64::from(i) * 0.02;
            OrderLevel::new(price, 1.5 + f64::from(i) * 0.01)
        })
        .collect();
    let asks = (0..64)
        .map(|i| {
            let price = 100.01 + f64::from(i) * 0.02;
            OrderLevel::new(price, 1.4 + f64::from(i) * 0.01)
        })
        .collect();
    let book = OrderBook::from_depth(bids, asks);
    let aggressive = OrderLevel::new(100.80, 28.0);
    (book, aggressive)
}

fn bench_match_core(c: &mut Criterion) {
    let (template, aggressive) = build_order_book();
    c.bench_function("match_core", |b| {
        b.iter_batched(
            || template.clone(),
            |mut book| {
                let outcome = match_core(&mut book, &aggressive, Side::Buy);
                black_box(outcome);
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench_match_core);
criterion_main!(benches);

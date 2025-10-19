//! Criterion microbenchmarks para os caminhos críticos do DEC.
//!
//! Funções auto-descobertas:
//! - match_core (matching de livro agregado)
//! - route_fast (roteamento em venues prioritários)
//! - twap_update (atualização incremental do TWAP)

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use trendmarketv2::dec::{
    match_core, route_fast, twap_update, OrderBook, OrderLevel, PriceSample, RouteContext, Side,
    TwapState, VenueQuote,
};
use trendmarketv2::MatchOutcome;

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
    c.bench_function("match_core_liquidity_sweep", |b| {
        b.iter_batched(
            || template.clone(),
            |mut book| {
                let outcome: MatchOutcome = match_core(&mut book, &aggressive, Side::Buy);
                black_box(outcome);
            },
            BatchSize::SmallInput,
        );
    });
}

fn build_route_context() -> (RouteContext, OrderLevel) {
    let quotes = (0..48)
        .map(|i| VenueQuote {
            venue: format!("venue-{:02}", i),
            price: 100.2 + (f64::from(i % 4) * 0.03),
            latency_ms: 20 + (i * 3) as u32,
            available_qty: 5.0 + f64::from(i) * 0.3,
            reliability: 0.85 + (f64::from(i % 5) * 0.03),
        })
        .collect();
    let ctx = RouteContext::new(120, 0.9, 0.02, 4.0, quotes);
    let order = OrderLevel::new(100.5, 18.0);
    (ctx, order)
}

fn bench_route_fast(c: &mut Criterion) {
    let (ctx, order) = build_route_context();
    c.bench_function("route_fast_path_selection", |b| {
        b.iter(|| {
            let decision = route_fast(black_box(&ctx), &order, Side::Buy);
            black_box(decision.expected_price);
        });
    });
}

fn bench_twap_update(c: &mut Criterion) {
    let mut state = TwapState::new(std::time::Duration::from_secs(300), 100.0, 0);
    let samples: Vec<PriceSample> = (1..=600)
        .map(|i| PriceSample {
            timestamp_ms: (i * 1_000) as u64,
            price: 100.0 + (i as f64).sin() * 1.5 + (i % 7) as f64 * 0.02,
        })
        .collect();

    c.bench_function("twap_update_sliding_window", |b| {
        b.iter_batched_ref(
            || state.clone(),
            |st| {
                for sample in &samples {
                    let twap = twap_update(st, *sample);
                    black_box(twap);
                }
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(
    name = dec_benches;
    config = Criterion::default();
    targets = bench_match_core, bench_route_fast, bench_twap_update
);
criterion_main!(dec_benches);

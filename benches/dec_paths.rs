use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use trendmarketv2::dec::{
    match_core, route_fast, twap_update, OrderBook, OrderLevel, PriceSample, RouteContext, Side,
    TwapState, VenueQuote,
};

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

fn build_route_context() -> RouteContext {
    let quotes = (0..48)
        .map(|i| VenueQuote {
            venue: format!("venue-{:02}", i),
            price: 100.2 + (f64::from(i % 4) * 0.03),
            latency_ms: 20 + (i * 3) as u32,
            available_qty: 5.0 + f64::from(i) * 0.3,
            reliability: 0.85 + (f64::from(i % 5) * 0.03),
        })
        .collect();
    RouteContext::new(120, 0.9, 0.02, 4.0, quotes)
}

fn compute_paths(
    mut book: OrderBook,
    mut ctx: RouteContext,
    order: &OrderLevel,
) -> (Vec<String>, f64) {
    let mut remaining = order.quantity;
    let mut venues = Vec::new();
    let mut twap_state = TwapState::new(Duration::from_secs(300), order.price, 0);
    let mut timestamp = 0u64;
    let mut last_twap = order.price;

    while remaining > 0.01 && !ctx.quotes.is_empty() {
        let decision = route_fast(&ctx, order, Side::Buy);
        let venue = match decision.venue {
            Some(v) => v,
            None => break,
        };

        let chunk_qty = (order.quantity / 4.0).max(1.0).min(remaining);
        let chunk = OrderLevel::new(order.price, chunk_qty);
        let outcome = match_core(&mut book, &chunk, Side::Buy);
        remaining = outcome.remaining;

        venues.push(venue.clone());
        ctx.quotes.retain(|q| q.venue != venue);

        timestamp += 15_000;
        last_twap = twap_update(
            &mut twap_state,
            PriceSample {
                timestamp_ms: timestamp,
                price: decision.expected_price,
            },
        );
    }

    (venues, last_twap)
}

fn bench_dec_paths(c: &mut Criterion) {
    c.bench_function("dec_paths", |b| {
        b.iter_batched(
            || {
                let (book, aggressive) = build_order_book();
                let ctx = build_route_context();
                (book, aggressive, ctx)
            },
            |(book, order, ctx)| {
                let (venues, twap) = compute_paths(book, ctx, &order);
                black_box((venues, twap));
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench_dec_paths);
criterion_main!(benches);

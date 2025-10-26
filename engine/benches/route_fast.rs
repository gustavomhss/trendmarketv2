use criterion::{black_box, criterion_group, criterion_main, Criterion};
use trendmarketv2::dec::{route_fast, OrderLevel, RouteContext, Side, VenueQuote};

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
    c.bench_function("route_fast", |b| {
        b.iter(|| {
            let decision = route_fast(black_box(&ctx), &order, Side::Buy);
            black_box((decision.expected_price, decision.score));
        });
    });
}

criterion_group!(benches, bench_route_fast);
criterion_main!(benches);

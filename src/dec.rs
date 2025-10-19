use std::cmp::Ordering;
use std::collections::VecDeque;
use std::time::Duration;

/// Sentido da ordem no livro.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Buy,
    Sell,
}

/// Representa um nível agregado no livro de ofertas.
#[derive(Clone, Debug)]
pub struct OrderLevel {
    pub price: f64,
    pub quantity: f64,
}

impl OrderLevel {
    pub fn new(price: f64, quantity: f64) -> Self {
        Self { price, quantity }
    }
}

/// Livro de ofertas resumido com agregação por nível de preço.
#[derive(Clone, Debug, Default)]
pub struct OrderBook {
    pub bids: Vec<OrderLevel>,
    pub asks: Vec<OrderLevel>,
}

impl OrderBook {
    /// Cria um livro a partir de níveis de oferta e demanda pré-ordenados.
    pub fn from_depth(bids: Vec<OrderLevel>, asks: Vec<OrderLevel>) -> Self {
        let mut book = Self { bids, asks };
        book.sort_levels();
        book
    }

    fn sort_levels(&mut self) {
        self.bids
            .sort_by(|a, b| b.price.partial_cmp(&a.price).unwrap_or(Ordering::Equal));
        self.asks
            .sort_by(|a, b| a.price.partial_cmp(&b.price).unwrap_or(Ordering::Equal));
    }

    fn book_side(&mut self, incoming: Side) -> &mut Vec<OrderLevel> {
        match incoming {
            Side::Buy => &mut self.asks,
            Side::Sell => &mut self.bids,
        }
    }
}

/// Resultado do processo de matching principal.
#[derive(Clone, Copy, Debug, Default)]
pub struct MatchOutcome {
    pub filled: f64,
    pub average_price: f64,
    pub remaining: f64,
}

/// Executa o matching básico de uma ordem contra o livro agregado.
pub fn match_core(book: &mut OrderBook, order: &OrderLevel, side: Side) -> MatchOutcome {
    let resting = book.book_side(side);
    let mut remaining = order.quantity;
    let mut notional = 0.0;
    let mut filled = 0.0;
    let mut idx = 0;

    while remaining > 0.0 && idx < resting.len() {
        let level = &mut resting[idx];
        if !price_crosses(side, order.price, level.price) {
            break;
        }

        let traded = remaining.min(level.quantity);
        if traded > 0.0 {
            remaining -= traded;
            filled += traded;
            notional += traded * level.price;
            level.quantity -= traded;
        }

        if level.quantity <= 1e-9 {
            resting.remove(idx);
        } else {
            idx += 1;
        }
    }

    MatchOutcome {
        filled,
        average_price: if filled > 0.0 { notional / filled } else { 0.0 },
        remaining,
    }
}

fn price_crosses(side: Side, aggressive: f64, passive: f64) -> bool {
    match side {
        Side::Buy => aggressive + f64::EPSILON >= passive,
        Side::Sell => aggressive - f64::EPSILON <= passive,
    }
}

/// Cotação por venue para roteamento rápido.
#[derive(Clone, Debug)]
pub struct VenueQuote {
    pub venue: String,
    pub price: f64,
    pub latency_ms: u32,
    pub available_qty: f64,
    pub reliability: f64,
}

/// Contexto de roteamento considerando restrições operacionais.
#[derive(Clone, Debug)]
pub struct RouteContext {
    pub tolerance_ms: u32,
    pub min_reliability: f64,
    pub penalty_per_ms: f64,
    pub risk_penalty: f64,
    pub quotes: Vec<VenueQuote>,
}

impl RouteContext {
    pub fn new(
        tolerance_ms: u32,
        min_reliability: f64,
        penalty_per_ms: f64,
        risk_penalty: f64,
        quotes: Vec<VenueQuote>,
    ) -> Self {
        Self {
            tolerance_ms,
            min_reliability,
            penalty_per_ms,
            risk_penalty,
            quotes,
        }
    }
}

/// Motivo associado à decisão de roteamento.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteDecisionReason {
    Selected,
    LatencyFiltered,
    ReliabilityFiltered,
    NoVenue,
}

/// Resultado do roteamento rápido.
#[derive(Clone, Debug)]
pub struct RouteDecision {
    pub venue: Option<String>,
    pub expected_price: f64,
    pub score: f64,
    pub reason: RouteDecisionReason,
}

/// Escolhe o venue mais adequado considerando latência, confiabilidade e capacidade.
pub fn route_fast(ctx: &RouteContext, order: &OrderLevel, side: Side) -> RouteDecision {
    let mut best: Option<(usize, f64)> = None;
    let mut latest_reason = RouteDecisionReason::NoVenue;

    for (idx, quote) in ctx.quotes.iter().enumerate() {
        if quote.latency_ms > ctx.tolerance_ms {
            latest_reason = RouteDecisionReason::LatencyFiltered;
            continue;
        }

        if quote.reliability < ctx.min_reliability {
            latest_reason = RouteDecisionReason::ReliabilityFiltered;
            continue;
        }

        let capacity_penalty = if quote.available_qty + 1e-9 < order.quantity {
            ctx.risk_penalty
        } else {
            0.0
        };

        let price_score = match side {
            Side::Buy => -quote.price,
            Side::Sell => quote.price,
        };

        let score =
            price_score - ctx.penalty_per_ms * f64::from(quote.latency_ms) - capacity_penalty
                + quote.reliability;

        match best {
            None => best = Some((idx, score)),
            Some((_, best_score)) if score > best_score => best = Some((idx, score)),
            _ => {}
        }
    }

    if let Some((idx, score)) = best {
        let selected = ctx.quotes[idx].clone();
        RouteDecision {
            venue: Some(selected.venue),
            expected_price: selected.price,
            score,
            reason: RouteDecisionReason::Selected,
        }
    } else {
        RouteDecision {
            venue: None,
            expected_price: order.price,
            score: f64::NEG_INFINITY,
            reason: latest_reason,
        }
    }
}

#[derive(Clone, Debug)]
struct PriceInterval {
    price: f64,
    duration: f64,
}

/// Estado incremental para cálculo de TWAP.
#[derive(Clone, Debug)]
pub struct TwapState {
    horizon: Duration,
    intervals: VecDeque<PriceInterval>,
    weighted_sum: f64,
    total_weight: f64,
    last_timestamp_ms: Option<u64>,
}

impl TwapState {
    pub fn new(horizon: Duration, initial_price: f64, initial_timestamp_ms: u64) -> Self {
        let mut intervals = VecDeque::new();
        intervals.push_back(PriceInterval {
            price: initial_price,
            duration: 0.0,
        });
        Self {
            horizon,
            intervals,
            weighted_sum: 0.0,
            total_weight: 0.0,
            last_timestamp_ms: Some(initial_timestamp_ms),
        }
    }
}

/// Amostra de preço a ser incorporada no TWAP.
#[derive(Clone, Copy, Debug)]
pub struct PriceSample {
    pub timestamp_ms: u64,
    pub price: f64,
}

/// Atualiza o TWAP incrementalmente garantindo janela deslizante determinística.
pub fn twap_update(state: &mut TwapState, sample: PriceSample) -> f64 {
    if let Some(last) = state.last_timestamp_ms {
        let delta_ms = sample.timestamp_ms.saturating_sub(last) as f64;
        if delta_ms > 0.0 {
            if let Some(last_interval) = state.intervals.back_mut() {
                let delta_secs = delta_ms / 1_000.0;
                last_interval.duration += delta_secs;
                state.weighted_sum += last_interval.price * delta_secs;
                state.total_weight += delta_secs;
            }
        }
    }

    state.last_timestamp_ms = Some(sample.timestamp_ms);
    state.intervals.push_back(PriceInterval {
        price: sample.price,
        duration: 0.0,
    });

    prune_horizon(state);
    compute_twap(state)
}

fn prune_horizon(state: &mut TwapState) {
    let horizon_weight = state.horizon.as_secs_f64();

    while state.total_weight > horizon_weight + 1e-12 {
        let excess = state.total_weight - horizon_weight;
        if let Some(mut front) = state.intervals.pop_front() {
            if front.duration <= excess + 1e-12 {
                state.weighted_sum -= front.price * front.duration;
                state.total_weight -= front.duration;
                continue;
            }

            front.duration -= excess;
            state.weighted_sum -= front.price * excess;
            state.total_weight -= excess;
            state.intervals.push_front(front);
            break;
        } else {
            break;
        }
    }
}

fn compute_twap(state: &TwapState) -> f64 {
    let horizon_weight = state.horizon.as_secs_f64();
    if horizon_weight <= 0.0 {
        return state.intervals.back().map(|i| i.price).unwrap_or_default();
    }

    if state.total_weight >= horizon_weight - 1e-9 {
        if state.total_weight <= 0.0 {
            return state.intervals.back().map(|i| i.price).unwrap_or_default();
        }
        return state.weighted_sum / state.total_weight;
    }

    let filler_price = state.intervals.back().map(|i| i.price).unwrap_or_default();
    let missing = horizon_weight - state.total_weight;
    let numerator = state.weighted_sum + filler_price * missing;
    numerator / horizon_weight
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn match_core_matches_until_price_cross() {
        let mut book = OrderBook::from_depth(
            vec![OrderLevel::new(101.2, 5.0), OrderLevel::new(101.0, 10.0)],
            vec![OrderLevel::new(101.4, 2.0), OrderLevel::new(101.6, 10.0)],
        );
        let incoming = OrderLevel::new(101.5, 3.0);
        let outcome = match_core(&mut book, &incoming, Side::Buy);
        assert!((outcome.filled - 2.0).abs() < 1e-9);
        assert!((outcome.average_price - 101.4).abs() < 1e-9);
        assert!((outcome.remaining - 1.0).abs() < 1e-9);
    }

    #[test]
    fn route_fast_filters_by_latency_and_reliability() {
        let ctx = RouteContext::new(
            50,
            0.9,
            0.01,
            2.0,
            vec![
                VenueQuote {
                    venue: "alpha".into(),
                    price: 101.5,
                    latency_ms: 40,
                    available_qty: 5.0,
                    reliability: 0.95,
                },
                VenueQuote {
                    venue: "beta".into(),
                    price: 101.4,
                    latency_ms: 80,
                    available_qty: 100.0,
                    reliability: 0.99,
                },
            ],
        );
        let order = OrderLevel::new(101.6, 3.0);
        let decision = route_fast(&ctx, &order, Side::Buy);
        assert_eq!(decision.venue.as_deref(), Some("alpha"));
        assert_eq!(decision.reason, RouteDecisionReason::Selected);
    }

    #[test]
    fn twap_update_handles_sliding_window() {
        let mut state = TwapState::new(Duration::from_secs(60), 100.0, 0);
        let mut price = 100.0;
        for step in 1..=6 {
            price += f64::from(step);
            twap_update(
                &mut state,
                PriceSample {
                    timestamp_ms: (step * 10_000) as u64,
                    price,
                },
            );
        }
        let twap = twap_update(
            &mut state,
            PriceSample {
                timestamp_ms: 70_000,
                price: 112.0,
            },
        );
        assert!(twap > 105.0 && twap < 112.0);
    }
}

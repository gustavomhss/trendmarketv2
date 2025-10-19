pub mod dec;

pub use dec::{
    match_core, route_fast, twap_update, MatchOutcome, OrderBook, OrderLevel, PriceSample,
    RouteContext, RouteDecision, RouteDecisionReason, Side, TwapState, VenueQuote,
};

/// Retorna true quando os módulos principais do DEC estão prontos para execução.
pub fn dec_engine_ready() -> bool {
    true
}

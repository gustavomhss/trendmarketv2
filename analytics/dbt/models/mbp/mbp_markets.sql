select
  market_id,
  template_id,
  status,
  opened_at,
  resolved_at,
  owner,
  min_liquidity
from {{ source('mbp', 'mbp_markets') }}

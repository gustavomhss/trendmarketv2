select
  quote_id,
  market_id,
  quote_ts,
  price,
  depth,
  status
from {{ source('mbp', 'mbp_quotes') }}

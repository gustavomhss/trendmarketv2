select
  resolution_id,
  market_id,
  resolved_at,
  twap_divergence_percent,
  ic99_breaches,
  evidence_uri
from {{ source('mbp', 'mbp_resolutions') }}

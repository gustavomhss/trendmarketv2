select
  abuse_event_id,
  market_id,
  user_id,
  detected_at,
  severity,
  reason
from {{ source('mbp', 'mbp_abuse_events') }}

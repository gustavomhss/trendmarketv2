with latest_quote as (
    select max(ts) as max_ts from {{ ref('stg_oracle_quotes') }}
)
select twap.*
from {{ ref('mrt_twap_5m') }} twap
cross join latest_quote
where datediff('second', twap.ts, latest_quote.max_ts) > 300


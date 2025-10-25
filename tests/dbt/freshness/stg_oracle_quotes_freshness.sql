select *
from {{ ref('stg_oracle_quotes') }}
where staleness_ms > 30000


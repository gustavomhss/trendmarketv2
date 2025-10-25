{{ config(materialized='table') }}

with quotes as (
    select * from {{ ref('stg_oracle_quotes') }}
),
minute_buckets as (
    select
        symbol,
        date_trunc('minute', ts) as window_start,
        avg(price) as avg_price,
        min(case when staleness_ms <= 30000 then 1 else 0 end) as quorum_ok
    from quotes
    group by 1, 2
)

select
    symbol,
    window_start as ts,
    avg_price as twap,
    (quorum_ok = 1) as quorum_ok
from minute_buckets;


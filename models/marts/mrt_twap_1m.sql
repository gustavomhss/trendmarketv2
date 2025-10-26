{{ config(materialized='table') }}

with quotes as (
    select * from {{ ref('stg_oracle_quotes') }}
), minute_buckets as (
    select
        symbol,
        date_trunc('minute', ts) as window_start,
        avg(price) as avg_price,
        max(staleness_ms) as max_staleness_ms
    from quotes
    group by 1, 2
)
select
    symbol,
    window_start as ts,
    avg_price as twap,
    max_staleness_ms
from minute_buckets

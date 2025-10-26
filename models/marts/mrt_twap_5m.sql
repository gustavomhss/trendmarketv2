{{ config(materialized='table') }}

with quotes as (
    select * from {{ ref('stg_oracle_quotes') }}
), windowed as (
    select
        symbol,
        window_start,
        avg(price) as avg_price,
        min(case when staleness_ms <= 30000 then 1 else 0 end) as quorum_ok
    from (
        select
            symbol,
            price,
            staleness_ms,
            date_trunc('minute', ts) - ((extract(minute from ts)::integer % 5)) * interval '1 minute' as window_start
        from quotes
    ) bucketed
    group by 1, 2
)
select
    symbol,
    window_start as ts,
    avg_price as twap,
    (quorum_ok = 1) as quorum_ok
from windowed

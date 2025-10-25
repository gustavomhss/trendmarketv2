{{ config(materialized='table') }}

with quotes as (
    select * from (
        values
            ('BRLUSD', timestamp '2024-01-01 00:00:00', 'primary', 5.4375, 1200),
            ('BRLUSD', timestamp '2024-01-01 00:00:20', 'secondary', 5.4380, 800),
            ('BRLUSD', timestamp '2024-01-01 00:00:40', 'tertiary', 5.4378, 500)
    ) as t(symbol, ts, source, price, staleness_ms)
)

select
    symbol,
    ts,
    source,
    price,
    staleness_ms
from quotes;


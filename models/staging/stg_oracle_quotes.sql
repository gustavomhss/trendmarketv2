{{ config(materialized='table') }}

select
    upper(symbol) as symbol,
    cast(ts as timestamp) as ts,
    lower(source) as source,
    cast(price as double) as price,
    cast(staleness_ms as integer) as staleness_ms
from {{ ref('oracle_quotes') }}

{{ config(materialized='table') }}

with typed_events as (
    select
        cast(id as varchar) as id,
        cast(ts as timestamp) as ts,
        upper(trim(symbol)) as symbol,
        lower(trim(action)) as action,
        trim(reason) as reason,
        trim(evidence_uri) as evidence_uri,
        lower(trim(actor)) as actor
    from {{ ref('moderation_events') }}
), ranked_events as (
    select
        *,
        lag(ts) over (partition by symbol order by ts) as previous_event_ts
    from typed_events
)
select
    id,
    ts,
    symbol,
    action,
    reason,
    evidence_uri,
    actor,
    coalesce(datediff('minutes', previous_event_ts, ts), 0) as minutes_since_previous_event
from ranked_events

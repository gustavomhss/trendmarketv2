{{ config(materialized='table') }}

with source_data as (
    select *
    from {{ ref('moderation_events') }}
),
casted as (
    select
        cast(id as varchar) as id,
        cast(ts as timestamp) as ts,
        cast(symbol as varchar) as symbol,
        cast(action as varchar) as action,
        cast(reason as varchar) as reason,
        cast(evidence_uri as varchar) as evidence_uri,
        cast(actor as varchar) as actor
    from source_data
),
validated as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor,
        lag(ts) over (partition by symbol order by ts) as previous_event_ts
    from casted
)

select
    id,
    ts,
    symbol,
    action,
    reason,
    evidence_uri,
    actor,
    case when previous_event_ts is null then 0 else datediff('minutes', previous_event_ts, ts) end as minutes_since_previous_event
from validated;

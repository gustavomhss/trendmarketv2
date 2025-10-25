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
with raw_events as (
    select *
    from read_csv_auto('seeds/moderation_events.csv', header=True)
),
typed_events as (
    select
        cast(id as varchar) as id,
        cast(ts as timestamp) as ts,
        upper(trim(symbol)) as symbol,
        lower(trim(action)) as action,
        trim(reason) as reason,
        trim(evidence_uri) as evidence_uri,
        lower(trim(actor)) as actor
    from raw_events
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
    actor
from typed_events;
from raw_events;

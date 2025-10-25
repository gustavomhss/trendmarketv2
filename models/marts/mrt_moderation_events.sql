{{ config(materialized='table') }}

with events as (
    select * from {{ ref('stg_moderation_events') }}
),
ranked as (
    select
        *,
        row_number() over (partition by symbol order by ts desc) as symbol_event_rank
    from events
)

select
    id,
    ts,
    symbol,
    action,
    reason,
    evidence_uri,
    actor,
    (symbol_event_rank = 1) as is_latest_event
from ranked;

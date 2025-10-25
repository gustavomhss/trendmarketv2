{{ config(materialized='table') }}

with ranked_events as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor,
        row_number() over (partition by symbol order by ts desc) as event_rank
    from {{ ref('stg_moderation_events') }}
    where action in ('pause', 'resume', 'review')
),
latest_events as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor
    from ranked_events
    where event_rank <= 3
)

select *
from latest_events;

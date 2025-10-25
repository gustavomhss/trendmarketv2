{{ config(materialized='table') }}

with source as (
    select * from {{ ref('stg_moderation_events') }}
)

select
    symbol,
    sum(case when action = 'pause' then 1 else 0 end) as pauses,
    sum(case when action = 'resume' then 1 else 0 end) as resumes,
    sum(case when action = 'appeal' then 1 else 0 end) as appeals,
    avg(case when resolved_ts is not null then datediff('second', action_ts, resolved_ts) end) as avg_resolution_seconds
from source
group by symbol;
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
with ranked_events as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor,
        minutes_since_previous_event,
        row_number() over (partition by symbol order by ts desc) as event_rank,
        lead(ts) over (partition by symbol order by ts desc) as next_event_ts,
        sum(case when action = 'pause' then 1 else 0 end) over (
            partition by symbol order by ts rows between unbounded preceding and current row
        ) as pause_count_to_date
    from {{ ref('stg_moderation_events') }}
),
recent_events as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor,
        minutes_since_previous_event,
        event_rank,
        case when next_event_ts is null then 0 else datediff('minutes', next_event_ts, ts) end as minutes_until_next_event,
        pause_count_to_date,
        case
            when event_rank = 1 and action = 'pause' then 'paused'
            when event_rank = 1 and action = 'resume' then 'active'
            when event_rank = 1 then 'under_review'
            else 'historical'
        end as moderation_state
    from events
    where event_rank <= 3
)

select *
from recent_events;

{{ config(materialized='table') }}

with events as (
    select *
    from {{ ref('stg_moderation_events') }}
),
aggregated as (
    select
        symbol,
        sum(case when action = 'pause' then 1 else 0 end) as pauses,
        sum(case when action = 'appeal' then 1 else 0 end) as appeals
    from events
    group by symbol
),
ranked_events as (
    select
        *,
        row_number() over (partition by symbol order by ts desc) as event_rank,
        lead(ts) over (partition by symbol order by ts desc) as next_event_ts,
        sum(case when action = 'pause' then 1 else 0 end) over (
            partition by symbol
            order by ts desc
            rows between unbounded preceding and current row
        ) as pause_count_to_date
    from events
),
latest_events as (
    select
        symbol,
        id,
        ts,
        action,
        reason,
        evidence_uri,
        actor,
        event_rank,
        minutes_since_previous_event,
        case when next_event_ts is null then 0 else datediff('minutes', next_event_ts, ts) end as minutes_until_next_event,
        pause_count_to_date,
        case
            when event_rank = 1 and action = 'pause' then 'paused'
            when event_rank = 1 and action = 'resume' then 'active'
            when event_rank = 1 then 'under_review'
            else 'historical'
        end as moderation_state
    from ranked_events
    where event_rank = 1
),
final as (
    select
        a.symbol,
        a.pauses,
        a.appeals,
        l.id,
        l.ts,
        l.action,
        l.reason,
        l.evidence_uri,
        l.actor,
        l.event_rank,
        l.minutes_since_previous_event,
        l.minutes_until_next_event,
        l.pause_count_to_date,
        l.moderation_state
    from aggregated a
    join latest_events l using (symbol)
)

select *
from final

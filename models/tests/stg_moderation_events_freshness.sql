with latest_event as (
    select max(ts) as max_ts from {{ ref('stg_moderation_events') }}
)
select events.*
from {{ ref('stg_moderation_events') }} events
cross join latest_event
where datediff('minute', events.ts, latest_event.max_ts) > 60;
select *
from {{ ref('stg_moderation_events') }}
where ts < timestamp '2024-01-01 00:00:00';

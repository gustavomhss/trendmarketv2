{{ config(materialized='table') }}

with events as (
    select * from (
        values
            ('mod-evt-1', 'BRLUSD', 'pause', 'moderation_bot', 'moderator', 'accepted', timestamp '2024-01-01 00:02:00', timestamp '2024-01-01 00:07:00'),
            ('mod-evt-2', 'BRLUSD', 'resume', 'moderation_bot', 'moderator', 'accepted', timestamp '2024-01-01 00:08:00', timestamp '2024-01-01 00:08:30'),
            ('mod-evt-3', 'BRLUSD', 'appeal', 'ops_user', 'operator', 'submitted', timestamp '2024-01-01 00:05:00', null)
    ) as t(event_id, symbol, action, actor, role, outcome, action_ts, resolved_ts)
)

select
    event_id,
    symbol,
    action,
    actor,
    role,
    outcome,
    action_ts,
    resolved_ts
from events;

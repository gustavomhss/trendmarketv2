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

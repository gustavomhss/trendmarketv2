{{ config(materialized='table') }}

with source as (
    select * from {{ ref('stg_simulation_runs') }}
)

select
    scenario,
    count(*) as run_count,
    sum(case when status = 'success' then 1 else 0 end) as success_count,
    avg(ttpv_ms) as avg_ttpv_ms,
    max(ttpv_ms) as max_ttpv_ms
from source
group by scenario;

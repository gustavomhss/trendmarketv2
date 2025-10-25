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
with runs as (
    select * from {{ ref('stg_simulation_runs') }}
),
metrics as (
with ranked_runs as (
    select
        id,
        scenario,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        run_duration_seconds,
        row_number() over (partition by scenario order by finished_at desc, started_at desc) as scenario_rank
        datediff('second', started_at, finished_at) as runtime_seconds,
        case when p95_latency_ms <= 800 then 'pass' else 'breach' end as latency_slo_status
    from runs
)

select
    id,
    scenario,
    started_at,
    finished_at,
    p95_latency_ms,
    result_path,
    runtime_seconds,
    latency_slo_status
from metrics;
        row_number() over (partition by scenario order by finished_at desc) as scenario_rank
    from {{ ref('stg_simulation_runs') }}
),
latest_per_scenario as (
    select
        scenario,
        id as latest_run_id,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        run_duration_seconds,
        case when p95_latency_ms <= 800 then 'pass' else 'breach' end as ttpv_slo_status,
        datediff('minutes', started_at, finished_at) as run_duration_minutes
    from runs
    where scenario_rank = 1
),
scenario_metrics as (
    select
        scenario,
        latest_run_id,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        run_duration_seconds,
        run_duration_minutes,
        ttpv_slo_status,
        datediff('hours', finished_at, max(finished_at) over ()) as hours_since_last_run
    from latest_per_scenario
)

select *
from scenario_metrics;

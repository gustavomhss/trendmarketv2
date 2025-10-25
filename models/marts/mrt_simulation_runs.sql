{{ config(materialized='table') }}

with runs as (
    select * from {{ ref('stg_simulation_runs') }}
),
metrics as (
    select
        id,
        scenario,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
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

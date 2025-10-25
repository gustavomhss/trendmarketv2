{{ config(materialized='table') }}

with source_data as (
    select *
    from {{ ref('simulation_runs') }}
),
casted as (
    select
        cast(id as varchar) as id,
        cast(scenario as varchar) as scenario,
        cast(started_at as timestamp) as started_at,
        cast(finished_at as timestamp) as finished_at,
        cast(p95_latency_ms as integer) as p95_latency_ms,
        cast(result_path as varchar) as result_path
    from source_data
),
validated as (
    select
        id,
        scenario,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        datediff('seconds', started_at, finished_at) as run_duration_seconds
    from casted
)

select *
from validated;

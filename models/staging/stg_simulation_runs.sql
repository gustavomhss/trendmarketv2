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
with raw_runs as (
    select *
    from read_csv_auto('seeds/simulation_runs.csv', header=True)
),
typed_runs as (
    select
        cast(id as varchar) as id,
        lower(trim(scenario)) as scenario,
        cast(started_at as timestamp) as started_at,
        cast(finished_at as timestamp) as finished_at,
        cast(p95_latency_ms as integer) as p95_latency_ms,
        trim(result_path) as result_path
    from raw_runs
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
select
    id,
    scenario,
    started_at,
    finished_at,
    p95_latency_ms,
    result_path
from typed_runs;
from raw_runs;

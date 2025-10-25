{{ config(materialized='table') }}

with runs as (
    select * from (
        values
            ('run-spike-1', 'spike', timestamp '2024-01-01 00:00:00', 'success', 420, 42),
            ('run-gap-1', 'gap', timestamp '2024-01-01 00:05:00', 'success', 510, 42),
            ('run-burst-1', 'burst', timestamp '2024-01-01 00:10:00', 'success', 610, 42)
    ) as t(run_id, scenario, started_at, status, ttpv_ms, seed)
)

select
    run_id,
    scenario,
    started_at,
    status,
    ttpv_ms,
    seed
from runs;
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

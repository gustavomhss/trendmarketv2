{{ config(materialized='table') }}

select *
from (
    select
        run_id,
        scenario,
        case when p95_latency_ms <= 750 then 'success' else 'failed' end as status,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        datediff('seconds', started_at, finished_at) as run_duration_seconds
    from (
        select
            cast(id as varchar) as run_id,
            lower(trim(scenario)) as scenario,
            cast(started_at as timestamp) as started_at,
            cast(finished_at as timestamp) as finished_at,
            cast(p95_latency_ms as integer) as p95_latency_ms,
            trim(result_path) as result_path
        from (
            select *
            from read_csv_auto('seeds/simulation_runs.csv', header=True)
        ) as raw_runs
    ) as typed_runs
) as finalized_runs

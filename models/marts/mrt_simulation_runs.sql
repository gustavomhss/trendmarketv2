{{ config(materialized='table') }}

with runs as (
    select *
    from {{ ref('stg_simulation_runs') }}
),
scenario_counts as (
    select
        scenario,
        count(*) as run_count,
        sum(case when status = 'success' then 1 else 0 end) as success_count
    from runs
    group by scenario
),
ranked_runs as (
    select
        *,
        row_number() over (partition by scenario order by finished_at desc, started_at desc) as scenario_rank,
        max(finished_at) over () as most_recent_finish_ts
    from runs
),
latest_per_scenario as (
    select
        scenario,
        run_id as latest_run_id,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path,
        run_duration_seconds,
        cast(run_duration_seconds as double) / 60.0 as run_duration_minutes,
        case when p95_latency_ms <= 800 then 'pass' else 'breach' end as ttpv_slo_status,
        datediff('hours', finished_at, most_recent_finish_ts) as hours_since_last_run
    from ranked_runs
    where scenario_rank = 1
),
combined as (
    select
        c.scenario,
        c.run_count,
        c.success_count,
        l.latest_run_id,
        l.started_at,
        l.finished_at,
        l.p95_latency_ms,
        l.result_path,
        l.run_duration_seconds,
        l.run_duration_minutes,
        l.ttpv_slo_status,
        l.hours_since_last_run
    from scenario_counts c
    join latest_per_scenario l using (scenario)
)

select *
from combined

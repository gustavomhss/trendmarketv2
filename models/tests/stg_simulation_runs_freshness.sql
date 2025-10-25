with latest_run as (
    select max(finished_at) as max_finished_at from {{ ref('stg_simulation_runs') }}
)
select runs.*
from {{ ref('stg_simulation_runs') }} runs
cross join latest_run
where datediff('minute', runs.finished_at, latest_run.max_finished_at) > 120;
select *
from {{ ref('stg_simulation_runs') }}
where finished_at < timestamp '2024-02-25 00:00:00';

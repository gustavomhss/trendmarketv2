select *
from {{ ref('stg_simulation_runs') }}
where finished_at < timestamp '2024-02-25 00:00:00';

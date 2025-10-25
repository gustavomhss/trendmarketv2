select *
from {{ ref('stg_simulation_runs') }}
where finished_at - started_at > interval '5 minutes';

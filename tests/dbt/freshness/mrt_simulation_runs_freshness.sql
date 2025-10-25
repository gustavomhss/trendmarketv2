select *
from {{ ref('mrt_simulation_runs') }}
where hours_since_last_run > 200;

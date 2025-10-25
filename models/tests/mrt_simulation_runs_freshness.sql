select *
from {{ ref('mrt_simulation_runs') }}
where p95_latency_ms > 800;

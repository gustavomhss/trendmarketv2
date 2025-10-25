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

{{ config(materialized='table') }}

with raw_runs as (
    select
        id,
        scenario,
        started_at,
        finished_at,
        p95_latency_ms,
        result_path
    from read_csv_auto('fixtures/simulation_runs.csv',
                       header=True,
                       types={'id': 'VARCHAR',
                              'scenario': 'VARCHAR',
                              'started_at': 'TIMESTAMP WITH TIME ZONE',
                              'finished_at': 'TIMESTAMP WITH TIME ZONE',
                              'p95_latency_ms': 'INTEGER',
                              'result_path': 'VARCHAR'})
)

select
    id,
    scenario,
    started_at,
    finished_at,
    p95_latency_ms,
    result_path
from raw_runs;

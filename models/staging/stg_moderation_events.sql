{{ config(materialized='table') }}

with raw_events as (
    select
        id,
        ts,
        symbol,
        action,
        reason,
        evidence_uri,
        actor
    from read_csv_auto('fixtures/moderation_events.csv',
                       header=True,
                       types={'id': 'VARCHAR',
                              'ts': 'TIMESTAMP WITH TIME ZONE',
                              'symbol': 'VARCHAR',
                              'action': 'VARCHAR',
                              'reason': 'VARCHAR',
                              'evidence_uri': 'VARCHAR',
                              'actor': 'VARCHAR'})
)

select
    id,
    ts,
    symbol,
    action,
    reason,
    evidence_uri,
    actor
from raw_events;

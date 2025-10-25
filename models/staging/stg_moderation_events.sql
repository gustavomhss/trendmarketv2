{{ config(materialized='table') }}

with raw_events as (
    select *
    from read_csv_auto('seeds/moderation_events.csv', header=True)
),
typed_events as (
    select
        cast(id as varchar) as id,
        cast(ts as timestamp) as ts,
        upper(trim(symbol)) as symbol,
        lower(trim(action)) as action,
        trim(reason) as reason,
        trim(evidence_uri) as evidence_uri,
        lower(trim(actor)) as actor
    from raw_events
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
from typed_events;
from raw_events;

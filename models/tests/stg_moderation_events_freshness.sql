select *
from {{ ref('stg_moderation_events') }}
where ts < timestamp '2024-01-01 00:00:00';

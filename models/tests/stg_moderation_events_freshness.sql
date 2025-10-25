select *
from {{ ref('stg_moderation_events') }}
where ts < timestamp '2024-02-25 00:00:00';

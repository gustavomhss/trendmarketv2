# Runbook — Moderation Pause & Appeal Flow

## Objetivo
Cumprir SLAs `MTTD ≤ 5m` e `MTTM ≤ 15m` para eventos de moderação do MBP e garantir trilha de auditoria completa.

## Detectar
1. Monitorar painel "Moderation Appeals Open" no dashboard `S5 MBP Scale` e alerta `moderation_backlog_high` (limite >3 appeals abertos).
2. Revisar `out/moderation/ops_report.json` e audit log JSONL em `out/moderation/audit.log` da execução mais recente.
3. Consultar logs do serviço (`logs/moderation/service.log`) buscando `APPEAL_SUBMITTED` sem `RESOLUTION_POSTED` >15m.
4. Validar RBAC via `scripts/moderation_rbac_check.sh --actor <user>` se houver suspeita de permissão incorreta.

## Mitigar
1. **Acelerar triagem**
   - Reatribuir caso para moderador disponível: `scripts/moderation_assign.py --symbol <symbol> --actor <moderator>`.
   - Disparar notificação manual para appeals atrasados (`scripts/moderation_notify.sh --appeal <id>`).
2. **Reativar mercados pausados**
   - Usar endpoint `/moderation/resume` com evidência documentada (ver audit JSONL).
   - Se pausa inválida, registrar override no audit log com `trace_id` compartilhado com incidente.
3. **Atualizar relatório operacional**
   - Regenerar `out/moderation/ops_report.json` via `python scripts/moderation_report.py`.
   - Anexar resumo ao ticket `INC-MODERATION` e indicar tempo total até resolução.

## Comunicação
- Postar atualização a cada 15 minutos no canal `#mbp-incident` até backlog <1.
- Escalar para Product/Legal quando pausa envolver abuso de mercado ou risco reputacional.
- Documentar follow-up na retro semanal com métricas de cumprimento SLA.

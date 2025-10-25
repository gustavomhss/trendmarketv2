# Runbook — Moderação: Pause / Appeals

## Objetivo
Garantir `mbp:moderation:pauses_total` controlado, `mbp:moderation:mttd_minutes ≤ 5` e `mbp:moderation:mttm_minutes ≤ 15`, restaurando mercados pausados somente quando segurança e quorum estiverem OK. O gatilho vem de `abuse_spike`, `moderation_pause` ou solicitações de appeals em massa.

## Detectar
1. Confirmar alerta no Slack (`#compliance` ou `#dec-incident`) e no PagerDuty (`moderation-oncall`).
2. Abrir o dashboard "S5 MBP Scale" e revisar os painéis **"Moderation Appeals Open"** e `Oracle Staleness` (para contexto).
3. Rodar as queries PromQL (salvar saída):
   ```promql
   mbp:moderation:pauses_total{env="prod"}
   mbp:moderation:appeals_open{env="prod"}
   mbp:moderation:mttd_minutes{env="prod"}
   ```
4. Validar se há correlação com `abuse.events.rate` ou `mbp:oracle:divergence_p95` (incidentes oráculo podem disparar pausas).

## Diagnóstico
1. **Estado atual** — Executar `kubectl exec deploy/moderation-service -n mbp -- cat /var/log/moderation/moderation.log | tail -n 50` para recuperar audit trail (hash, actor, outcome).
2. **Fluxo Appeals** — Gerar relatório com `python - <<'PY' ... PY` lendo `moderation.log` e emitindo `out/obs_gatecheck/evidence/moderation_ops_report.json` (calcule MTTD/MTTM e contagem de appeals) para confirmar SLA.
   ```bash
   python - <<'PY'
   import calendar, json, statistics, time
   from pathlib import Path

   log = Path('/var/log/moderation/moderation.log')
   out = Path('out/obs_gatecheck/evidence/moderation_ops_report.json')
   records = []
   if log.exists():
       for line in log.read_text().splitlines():
           if line.strip():
               records.append(json.loads(line))
   pauses = [r for r in records if r['action'] == 'pause']
   appeals = [r for r in records if r['action'] == 'appeal']
   mttr = []
   for pause in pauses:
       resumed = next((r for r in records if r['action'] == 'resume' and r['target'] == pause['target'] and r['ts'] >= pause['ts']), None)
       if resumed:
           mttr.append((time.strptime(resumed['ts'], '%Y-%m-%dT%H:%M:%SZ'), time.strptime(pause['ts'], '%Y-%m-%dT%H:%M:%SZ')))
   now = time.time()
   report = {
       'pauses_total': len(pauses),
       'appeals_open': len(appeals),
       'mttd_minutes': statistics.mean([(now - calendar.timegm(time.strptime(p['ts'], '%Y-%m-%dT%H:%M:%SZ'))) / 60 for p in pauses]) if pauses else 0,
       'mttr_minutes': statistics.mean([(calendar.timegm(end) - calendar.timegm(start)) / 60 for end, start in mttr]) if mttr else 0,
   }
   out.parent.mkdir(parents=True, exist_ok=True)
   out.write_text(json.dumps(report, indent=2))
   print(f'[moderation_report] saved {out}')
   PY
   ```
3. **Integração Oráculos** — Caso o motivo seja divergência, verificar runbook `docs/runbooks/oracle-quorum-twap.md` antes de reabrir mercado.
4. **Auto-resolve** — `kubectl logs deploy/auto-resolution -n mbp --since=15m | rg -i 'moderation|appeal'` para ver decisões automáticas.
5. **Backlog** — Listar appeals pendentes via API (`curl -s -H "Authorization: Bearer $TOKEN" https://api.trendmarketv2.dev/moderation/appeals`).

## Mitigar
1. **Pause manual** — Se necessário, reforçar pausa: `curl -XPOST https://api.trendmarketv2.dev/moderation/pause -d '{"symbol":"BRLUSD","reason":"oracle_divergence"}'` (actor `moderator`). Registrar `trace_id`.
2. **Apelações** — Priorizar appeals críticos (`severity=blocker`). Notificar `pm.dec` quando o backlog > 5. Use `services/moderation/service.py` para importar log offline se API indisponível.
3. **Reabertura** — Quando o motivo original estiver mitigado e `mbp:moderation:appeals_open ≤ 1`, executar `curl -XPOST .../moderation/resume` e confirmar `trace_id` no log.
4. **Comunicação** — Atualizar canal público/status page com motivo, escopo, ETA e passos de mitigação.
5. **Prevenção** — Se a causa foi abuso, acionar equipe SEC para recalibrar regras (`auto_resolution/policies`). Para falhas de oráculo, alinhar com runbook de quorum.

## Evidência ORR
- Persistir as consultas PromQL em `out/obs_gatecheck/evidence/moderation_metrics.json`.
- Exportar últimos 20 eventos do log para `out/obs_gatecheck/logs/moderation_audit_tail.json` (usar `jq` para estruturar).
- Anexar captura da fila de appeals pós-normalização (`out/obs_gatecheck/evidence/moderation_dashboard.png`).
- Atualizar `out/obs_gatecheck/evidence/moderation_ops_report.json` com MTTD/MTTM reais e decisões tomadas.

## Comunicação & Escalonamento
- Reportar início/fim no Slack `#compliance` e `#dec-incident`.
- PagerDuty: escalar para `legal-oncall` se `appeals_open > 10` por mais de 30 min ou se houver impacto regulatório.
- Registrar ticket `CAPA-MOD` em até 24h com causas, métricas e links para evidências.

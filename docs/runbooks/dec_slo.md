# Runbook — DEC SLO

## Objetivo
Garantir DEC p95 ≤ 800 ms por 60 min a 120 rps com 5xx=0.

## Limites Operacionais
- Pool de conexões DB: 256.
- Conexões HTTP upstream: 512 (keep-alive ON).
- Timeout upstream: 450 ms.
- Alocador: `jemalloc` habilitado.

## Procedimento
1. Validar alerta `DECPerformanceDegradation` por 5 minutos.
2. Confirmar `slo_budget_breach` > 1 e logs sem PII.
3. Aplicar degrade: ativar cache quente, reduzir features opcionais, reforçar GC.
4. Se p95 > 0.8 s por mais 5 minutos, iniciar rollback completo.
5. Monitorar métrica `dec:recovered:10m` até retornar a 1.
6. Após recuperação, remover degrade e registrar incidente.

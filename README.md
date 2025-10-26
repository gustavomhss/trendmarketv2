# TrendMarketV2 — Observabilidade (CRD-8)

## Como tornar real

1. Configure os **secrets** no repositório/ambiente: `PROM_URL`, `APM_URL`, `GRAFANA_URL`, `LOKI_URL`, `OTEL_URL`, `SLACK_WEBHOOK_URL`, `L2_ENDPOINT` (opcional), `L2_WALLET`, `L2_PRIVATE_KEY`, `WORM_BUCKET`, `WORM_REGION`.
2. Torne o job **MBP S2 ORR** obrigatório na proteção de branch `main`.
3. Garanta os dashboards no Grafana com UIDs `dec-perf-ovw`, `mbp-e2e-span`, `fe-rum-core` apontando para as fontes declaradas nos seeds.
4. Prepare a wallet L2 com saldo suficiente e acesso auditável; mantenha um bucket WORM (write-once) com retenção ≥ 90 dias.
5. Ao ativar modo real, rode `scripts/orr_all.sh --real` para que hooks e provenance utilizem integrações reais.

```
┌────────────────────────────────────────────────────────────────────┐
│ GitHub Action: MBP S2 ORR                                          │
├───────────────┬────────────────────────┬───────────────────────────┤
│ analysis/run  │ hooks (A110 fast)      │ policy_engine + env_dump  │
├───────────────┴──────────────┬─────────┴───────────────┬──────────┤
│ bundle.sha256 → provenance   │ spec_check + refmap     │ hash_manifest │
└──────────────────────────────┴─────────────────────────┴──────────┘
                 ↓                        ↓                      ↓
            out/obs_gatecheck       PR comment DX         artifacts ORR
```

### Contrato do EVID (evidence directory)

Precedência: **Ambiente (`EVID`)** → **Flag CLI (`--out`/`--evidence`)** → **Default** (`out/obs_gatecheck/evidence`).
Todos os scripts aceitam `--out`/`--evidence` e respeitam `EVID` se definido.

## Tempo-alvo de publicação on-chain

* **SLO:** publicar `merkle_root` + `bundle.sha256` em ≤ 5 minutos após `STATUS: PASS`.
* **Fallback:** utilizar Base Sepolia em modo `--dry-run` + WORM até que `L2_ENDPOINT`/wallet estejam ativos.
* **Procedimento real:** executar `bash scripts/provenance/publish_root.sh --evidence out/obs_gatecheck/evidence` sem `--dry-run` com as variáveis `L2_*` presentes.

## Como rodar o pipeline

1. Execute localmente: `RUN_PROFILE=fast bash scripts/orr_all.sh --seed-dir seeds` (modo rápido) ou `RUN_PROFILE=full bash scripts/orr_all.sh --seed-dir seeds` (modo completo).
2. Confira `out/obs_gatecheck/evidence/spec_check.txt` (esperado `RESULT=PASS`).
3. Inspecione `out/obs_gatecheck/evidence/analysis/index.html` para o índice de evidências (botão “Copiar comando”).
4. O bundle completo e hashes ficam em `out/obs_gatecheck/evidence/` e `out/sim/` (SimCity fast + nightly).

## CI — GitHub Actions

* Workflow: `.github/workflows/_mbp-s2-orr.yml` (job **MBP S2 ORR**).
* Passos chave: dependências mínimas → `bash scripts/orr_all.sh` → validação `spec_check.txt` → artefato `orr-evidence` → comentário estruturado com hashes, merkle e links.
* Shellcheck roda de forma advisory (não bloqueia).

## Estrutura útil

* `docs/spec/SPEC.md` — especificação Lamport-style (INV1..INV5, LF1..LF2).
* `docs/mbp/sprint-2/` — resultados, manifesto de políticas e orçamento de cardinalidade.
* `configs/policies/` — composição de políticas (`project < env < mbp_s2`).
* `scripts/` — automações determinísticas (analysis, hooks, provenance, simulações, ORR).
* `sim/scenarios/` — cenários SimCity Sprint 2.
* `seeds/` — sementes versionadas por domínio para garantir reproducibilidade.

## Após merge

* Proteja `main` exigindo o job **MBP S2 ORR**.
* Gere tag pós-ORR se necessário seguindo o plano trimestral.

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

Precedência: **Ambiente (`EVID`)** → **Flag CLI (`--out`/`--evidence`)** → **Default** (`out/s4_orr/EVI`).
Todos os scripts aceitam `--out`/`--evidence` e respeitam `EVID` se definido.

## Tempo-alvo de publicação on-chain

* **SLO:** publicar `merkle_root` + `bundle.sha256` em ≤ 5 minutos após `STATUS: PASS`.
* **Fallback:** utilizar Base Sepolia em modo `--dry-run` + WORM até que `L2_ENDPOINT`/wallet estejam ativos.
* **Procedimento real:** executar `bash scripts/provenance/publish_root.sh --evidence out/obs_gatecheck/evidence` sem `--dry-run` com as variáveis `L2_*` presentes.

## Como rodar o pipeline

1. Rode `make prega` para executar o gate Sprint 4 completo (ORR real, dbt docs, flamegraphs, bundle).
2. Valide os logs em `out/s4_orr/` e confirme os marcadores `ACCEPTANCE_OK` e `GATECHECK_OK` em `out/s4_orr/EVI/`.
3. Inspecione os artefatos do dbt em `data/analytics/dbt/target/` e os diffs de schema em `out/s4_orr/EVI/schema_diff.txt`.
4. O bundle e SHA ficam em `out/s4_evidence_bundle_*.zip` e `out/s4_evidence_bundle_*.zip.sha256`.

## CI — GitHub Actions

* Workflow: `.github/workflows/_s4-orr.yml` (job **Sprint 4 ORR**).
* Passos chave: checkout → `make prega` → upload de artefatos (dbt docs, bundle) → publicação do resumo.
* Shellcheck roda de forma advisory (não bloqueia).

## Estrutura útil

* `docs/spec/SPEC.md` — especificação Lamport-style (INV1..INV5, LF1..LF2).
* `docs/mbp/sprint-2/` — resultados, manifesto de políticas e orçamento de cardinalidade.
* `engine/` — código do Decision Engine (Rust) e benches.
* `data/cdc/` — contratos, schemas e seeds versionados.
* `data/analytics/dbt/` — modelos analíticos e artefatos dbt.
* `obs/ops/` — infraestrutura de observabilidade (Prometheus, Otel, watchers).
* `scripts/` — automações determinísticas (analysis, hooks, provenance, ORR, bundle).

## Após merge

* Proteja `main` exigindo o job **Sprint 4 ORR** (`_s4-orr.yml`).
* Gere tag pós-ORR se necessário seguindo o plano trimestral.

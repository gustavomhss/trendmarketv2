# AGENTS.md — CreditEngine Codex Engineer

> **REPO CANÔNICO**: Todas as ações do agente devem ocorrer **exclusivamente** em `gustavomhss/trendmarketv2`.
> Qualquer referência a `credit-engine-core` é **erro** e deve ser corrigida automaticamente (substituir por `trendmarketv2`) ou abortar com mensagem clara.

> Arquivo curto, consumível por agentes (Codex/VS Code MCP/Agents SDK). Fonte de verdade em `docs/dna/`. Este guia especifica **o que** fazer; o **como** está nos artefatos da KB.

## TL;DR — Comandos Canônicos
- **Setup**
  - `brew bundle` (se macOS) → `cargo fetch` → `cargo build`
- **Testes & Linters**
  - `cargo test`
  - `cargo clippy -- -D warnings`
  - `cargo fmt -- --check`
- **Segurança**
  - `cargo deny check`
  - `cargo audit`
- **ORR / Bundle**
  - `bash scripts/orr_all.sh`
  - Esperar linhas de sucesso: `ACCEPTANCE_OK` e `GATECHECK_OK`
  - Artefatos: `out/obs_gatecheck/bundle.zip` e `out/obs_gatecheck/bundle.sha256.txt`
- **Abort imediato**
  - Qualquer teste/linters falham; `deny`/`audit` crítico; Prometheus target **DOWN**; qualquer watcher termina com `*_FAIL`

## Fonte de Verdade (KB)
- **Ler sempre antes de operar**: `docs/dna/`
  - `docs/dna/Leasson Learned so far v1.md`
  - Blocos e Master List `A1–A110` (inclui watchers A110)
  - "Manual do Agente", "Instruções do Agente", "Product Brief", "Spec Master"
- **Regra de ouro**: Se algo aqui divergir da KB, **vence a KB**.

## Fronteiras de Escrita (Allow/Deny)
- **ALLOW (leitura & escrita)**: `src/`, `tests/`, `ops/`, `scripts/`, `out/obs_gatecheck/`
- **READ‑ONLY**: `docs/dna/` (nunca editar), arquivos de licença e manifestos legais
- **DENY**: remover/renomear pastas canônicas; apagar evidências geradas por runs anteriores sem registrar no bundle

## Autonomia, Aprovação e Abort
- **Pode prosseguir sem confirmação** quando: alteração é local, atômica e coberta por testes/linters; sem efeitos fora do allowlist.
- **Pedir confirmação** quando: mudar contrato público; quebrar compatibilidade; introduzir dependência; alterar dashboards ou SLOs; mudanças > 200 LOC.
- **Abortar** imediatamente se: 
  - `cargo test` falha; `clippy` acusa `-D warnings`; `fmt --check` falha
  - `cargo deny check`/`cargo audit` com findings **críticos**
  - `promtargets` indicam `otelcol` ou alvos essenciais **DOWN**
  - qualquer watcher imprime `*_FAIL`
- Em caso de abort: **não** comitar. Emitir relatório curto (motivo, logs, sugestão de correção) e sair.

## MCP Tools/Resources (VS Code / Codex CLI)
- `filesystem: ./` (RW nas pastas do allowlist; RO em `docs/dna/`)
- `prom: http://127.0.0.1:9090` (R)
- `loki: http://127.0.0.1:3101` (R)
- `tempo/jaeger: http://127.0.0.1:3200` (R)
- `otelcol health: http://127.0.0.1:13133/healthz` (R)
- **Observação**: Endpoints e portas podem variar — ver `docs/dna/` e `ops/otel/*`.

## Mapa do Repositório (alvos do agente)
- `src/amm/` — núcleo CPMM (swap/liquidity/pricing/guardrails/types/errors)
- `tests/` — unitários, golden, propriedades, fuzz
- `ops/otel/` — coletores/pipelines de telemetria
- `ops/obs/` — catálogo de fontes e padrões (`sources.yaml`)
- `scripts/` — automações ORR e watchers (`orr_all.sh`, `obs_*_check.sh`)
- `out/obs_gatecheck/` — evidências e pacotes

## Ciclo Operacional (Entrada→Saída)
1) **Intake**: objetivo + restrições + SLOs (ver `docs/dna/`).
2) **Plano atômico**: passos pequenos, invariantes explícitos, arquivos-alvo.
3) **Implementar**: código idempotente, instrumentado (OTel/Prom) quando aplicável.
4) **Provar**: testes (unit/golden/propriedades/fuzz) + linters.
5) **ORR**: gerar bundle + manifest + SHA‑256; validar watchers.
6) **PR**: diffs limpos, checklist DoD verde, link para evidências.

## DoD (Definition of Done)
- Build `test` e `release` OK; `clippy` zero warnings; `fmt` aplicado
- Testes unit/golden/propriedades/fuzz **verdes** (bordas: under/overflow/zero/extremos/fees)
- Observabilidade mínima conforme KB; sem regressão de SLO local
- `cargo deny check` e `cargo audit` sem críticos
- `scripts/orr_all.sh` gerou `ACCEPTANCE_OK` e `GATECHECK_OK`; bundle + hash presentes
- Sem placeholders/TODO/`println!` supérfluos em código de produção

## Linhas de Sucesso Esperadas
- `ACCEPTANCE_OK`
- `GATECHECK_OK`
- `OTEL_METRICS ...` (cabeçalho presente quando coletores sobem)
- `PROM_READY` (quando aplicável)

## Notas sobre o AMM (CPMM)
- Invariantes e arredondamentos **obrigatórios** conforme KB (ver `docs/dna/`)
- Regras de `get_amount_out` e `get_amount_in` com arredondamentos explícitos; limites e monotonicidade
- Golden‑suite e propriedades obrigatórias para mudanças nesse módulo

## Segurança & Dependências
- Manter versões pinadas no `Cargo.toml`
- Executar `cargo deny check` & `cargo audit` em cada entrega
- Se necessário, alinhar patches conforme política da KB

## Git/PR
- Branch por tarefa; commits atômicos
- PR descreve objetivo, invariantes, artefatos tocados, comandos para reproduzir
- Anexar hash do bundle e caminho `out/obs_gatecheck/`

## Quickstart
```bash
brew bundle && cargo fetch && cargo build
cargo test && cargo clippy -- -D warnings && cargo fmt -- --check
cargo deny check && cargo audit
bash scripts/orr_all.sh
```

## Uso com Agents SDK
- Carregar este `AGENTS.md` como **instructions** do agente "Engenheiro CE"
- Injetar variáveis de ambiente/endpoints se divergirem do padrão
- Fornecer permissões RW apenas ao allowlist

## Uso com VS Code (MCP)
- Habilitar MCP no cliente; expor `filesystem: ./` e endpoints listados
- Confirmar descoberta do `AGENTS.md` na raiz do repo

## Quando em dúvida
- Consultar `docs/dna/` e watchers A110
- Preferir passos menores e provas executáveis
- Se a KB não cobre, abrir PR com ADR mínimo e pedir confirmação


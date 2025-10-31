# Storyboard — Q2-S7-Stabilize

## Deliverables (DbC)
### D1 — Sprint Guard instrumentation
Estruturar trio YAMLs e guardiões para a sprint corrente, garantindo documentação e schemas versionados em .sprint/.
**Require**: Schemas de deliverables/gates/filemap definidos para a sprint.
**Ensure**: Scripts sprint_guard e render_storyboard utilizam os YAMLs atualizados.
**Invariants**: Execuções repetidas permanecem idempotentes.

### D2 — Guardrails operacionais
Pinar GitHub Actions, validar SIGNATURE_PATH e garantir geração de storyboard e scorecard da sprint.
**Require**: Scripts de automação atualizados sob controle de versão.
**Ensure**: Evidências em out/evidence/* e scorecards produzidos pelo guard.
**Invariants**: Caminhos de assinatura permanecem fora do código de produção.

## Gates
### G1-PINS — GitHub Actions pin check
Garantir que actions críticas estejam pinadas por SHA.
**Require**: Refs de checkout/upload/download/setup-python precisam estar fixadas.
**Ensure**: Relatório de pins atualizado em out/evidence/T2_pins/.
**Run**:
- `python3 scripts/pin_actions.py`
- `python3 scripts/sprint_guard.py check-pins`
**Evidence**:
- `out/evidence/T2_pins/report.json`

### G2-CRYPTO — Assinaturas roundtrip
Validar sign/verify end-to-end usando vetores de teste da sprint.
**Require**: Dependências vendored disponíveis sem acesso externo.
**Ensure**: Bateria pytest sinaliza sucesso para roundtrip.
**Run**:
- `pytest -q tests/test_signature.py -k roundtrip`
**Evidence**:
- `out/evidence/T5_crypto`

## Filemap
- `.sprint/deliverables.yml` — Definição dos deliverables da sprint.
- `.sprint/gates.yml` — Gates de verificação automatizados.
- `.sprint/filemap.yml` — Inventário das evidências relevantes.
- `.sprint/schemas/deliverables.schema.yaml` — Schema de validação dos deliverables.
- `.sprint/schemas/gates.schema.yaml` — Schema de validação dos gates.
- `.sprint/schemas/filemap.schema.yaml` — Schema de validação do filemap.
- `scripts/pin_actions.py` — Automação para pinagem de GitHub Actions.
- `scripts/crypto/sign_batch.py` — Atualização do caminho de assinatura e diretório de evidências.
- `yaml/__init__.py` — Fallback local para carregamento de YAML sem rede.
- `docs/Storyboard.md` — Storyboard consolidado da sprint.
- `out/scorecards/sprint_guard_scorecard.json` — Scorecard gerado pelo Sprint Guard.
- `.github/pull_request_template.md` — Template padronizado de PR para Sprint Guard.

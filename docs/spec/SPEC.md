# SPEC — MBP Sprint 2 (Lamport-Style)

## Variáveis
- `State ∈ {PLAN_OK, EXEC_FAST_OK, EXEC_FULL_OK, ORR_OK, CANARY_READY}`
- `Metrics = {lat_p95_ms, err5xx_rate, burn4h, invariant, inp_p75_ms, obs_uptime}`
- `Policy = {thresholds, abort_rules, hash}`
- `Evidence = {bundle_sha256, merkle_root, tx_hash_or_worm, signatures_2ofN, histogram_schema_ver}`

## Init
`State = PLAN_OK ∧ ReadinessOk ∧ MetricsPresent ∧ Policy.hash = policy_hash.txt ∧ Evidence.histogram_schema_ver = env_dump.txt:HistogramSchemaVersion`

## Ações
- **Collect**: atualiza `Metrics` com janelas consistentes; `clock_skew ≤ 120s`; `cdc_lag_p95 ≤ 120s`.
- **InjectFault**: executa qualquer hook A110 com idempotência (`--real` opcional); mantém rastreabilidade.
- **EvaluatePolicy**: se `Abort` ⇒ rollback/freeze e `State` inalterado; se `PromoteOk` ⇒ `State := Next(State)`; caso contrário `State` permanece.
- **FinalizeEvidence**: materializa `bundle.sha256.txt`, `merkle_root`, `tx_hash_or_worm`, `signatures.json` 2-de-N.

## Invariantes (Safety)
- **INV1 EvidenceBound**: `bundle_sha256` ∧ (`merkle_root` ∧ `tx_hash` ∨ `worm_proof`) ∧ `signatures_2ofN` válido.
- **INV2 InvariantZero**: `Metrics.invariant = 0` em shadow/canary.
- **INV3 NoPromoteOnBurn**: `Metrics.burn4h ≥ 1` ⇒ `State ≠ CANARY_READY`.
- **INV4 DeterministicPolicy**: `policy_hash` idêntico ∧ métricas idênticas ⇒ decisão idêntica.
- **INV5 NoDataNoProgress**: ausência de métricas essenciais implica `AbortOrHold`.

## Progresso (Liveness)
- **LF1 Progress**: `ReadinessOk ∧ ¬Abort(Metrics,Policy) ~> CANARY_READY` (fairness fraca para `Collect`/`EvaluatePolicy`).
- **LF2 Recovery**: Após `Abort`, com métricas dentro dos thresholds, `EvaluatePolicy` permite avanço.

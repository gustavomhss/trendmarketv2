"""Prompt extras for TrendMarket MBP rollout scenarios."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, Sequence, Tuple


@dataclass(frozen=True)
class SafetyProofSketch:
    """Lamport-style micro safety proof sketch for the rollout pipeline."""

    variables: Dict[str, str]
    invariants: Sequence[Tuple[str, str]]
    progress: Sequence[Tuple[str, str]]
    conclusion: str

    def to_markdown(self) -> str:
        lines = ["## 1) Micro Safety Proof Sketch (Lamport-style)"]
        lines.append("")
        lines.append("**Variáveis**")
        for name, description in self.variables.items():
            lines.append(f"* `{name}` = {description}")
        lines.append("")
        lines.append("**Invariantes**")
        for key, description in self.invariants:
            lines.append(f"* **{key}** {description}")
        lines.append("")
        lines.append("**Progresso**")
        for key, description in self.progress:
            lines.append(f"* **{key}** {description}")
        lines.append("")
        lines.append(f"**Conclusão**: {self.conclusion}")
        return "\n".join(lines)


@dataclass(frozen=True)
class TelemetryHook:
    """Telemetry helpers describing decision counters and tracing hooks."""

    description: str
    node_snippet: str
    python_snippet: str
    quick_commands: Sequence[Tuple[str, str]]
    promql: Sequence[str]

    def to_markdown(self) -> str:
        lines = ["## 2) Telemetria de decisão (Kay)"]
        lines.append("")
        lines.append(self.description)
        lines.append("")
        lines.append("### 2.1 Node/Express (OTel API)")
        lines.append("\n```js")
        lines.append(self.node_snippet.strip())
        lines.append("```")
        lines.append("")
        lines.append("### 2.2 Python/FastAPI (OTel API)")
        lines.append("\n```python")
        lines.append(self.python_snippet.strip())
        lines.append("```")
        lines.append("")
        lines.append("### ⚡ Ativação rápida (1 comando)")
        for title, command in self.quick_commands:
            lines.append("")
            lines.append(f"* **{title}**:")
            lines.append("\n```bash")
            lines.append(command.strip())
            lines.append("```")
        lines.append("")
        lines.append("### 🔎 Consulta Prom (validação rápida)")
        for query in self.promql:
            lines.append("")
            lines.append("```promql")
            lines.append(query.strip())
            lines.append("```")
        return "\n".join(lines)


@dataclass(frozen=True)
class TypedVariants:
    """Typed implementations for shadow/canary logic in TS and Python."""

    ts_snippet: str
    py_snippet: str

    def to_markdown(self) -> str:
        lines = ["## 3) Variantes tipadas (Knuth) — TS e pydantic"]
        lines.append("")
        lines.append("### 3.1 TypeScript — Shadow + Canary (Express)")
        lines.append("\n```ts")
        lines.append(self.ts_snippet.strip())
        lines.append("```")
        lines.append("")
        lines.append("### 3.2 Python — Pydantic Settings para o YAML")
        lines.append("\n```python")
        lines.append(self.py_snippet.strip())
        lines.append("```")
        return "\n".join(lines)


@dataclass(frozen=True)
class LivenessNote:
    """Operational liveness reminder for canary percent changes."""

    statement: str
    conditions: Sequence[str]
    steps: Sequence[str]
    observations: Sequence[str]

    def to_markdown(self) -> str:
        lines = ["## 4) Liveness note — mudança de percent no canário"]
        lines.append("")
        lines.append("**Enunciado.** " + self.statement)
        lines.append("")
        lines.append("**Condições.**")
        for condition in self.conditions:
            lines.append(f"* {condition}")
        lines.append("")
        lines.append("**Operacional (2 passos).**")
        for index, step in enumerate(self.steps, start=1):
            lines.append(f"{index}. {step}")
        lines.append("")
        for note in self.observations:
            lines.append(note)
        return "\n".join(lines)


def _safety_proof_defaults() -> SafetyProofSketch:
    return SafetyProofSketch(
        variables={
            "Resp": "resposta principal ao usuário",
            "ShadowReq": "cópia enviada ao alvo shadow",
            "Cfg": "conteúdo efetivo de `configs/rollout/mbp_canary.yml` (ou default seguro)",
        },
        invariants=(
            (
                "INV-S1",
                "(Shadow non-interference): `Resp` independe do sucesso de `ShadowReq`.",
            ),
            (
                "INV-C1",
                "(Canary default-safe): `Cfg.canary.enabled = false` ⇒ tráfego = `stable`.",
            ),
            (
                "INV-C2",
                "(Graceful fallback): `Cfg` inválida/ausente ⇒ usar `Cfg_default` com `enabled=false`.",
            ),
            (
                "INV-R1",
                "(Rollback 1-passo): `edit(Cfg.enabled=false)` + `restart` ⇒ tráfego reverte integralmente a `stable`.",
            ),
        ),
        progress=(
            (
                "LF-S",
                "Se `SHADOW_ENABLED=true` e `/mbp/*` recebe tráfego, então `ShadowReq` é emitida fire-and-forget (sem bloquear `Resp`).",
            ),
            (
                "LF-C",
                "Se `Cfg.canary.enabled=true` e `percent=p`, para usuários internos, uma fração estável ≈p% será roteada para `canary` por hashing determinístico.",
            ),
        ),
        conclusion=(
            "As propriedades acima garantem que o sistema é fail-safe (nenhuma falha do shadow ou do YAML quebra a resposta) "
            "e reversível (rollback imediato via edição de `Cfg`)."
        ),
    )


def _telemetry_defaults() -> TelemetryHook:
    description = (
        "Publique um evento/contagem por decisão (`canary`/`stable`) e opcionalmente um span para rastreabilidade. "
        "Exemplos mínimos com OpenTelemetry."
    )
    node_snippet = """
// src/rollout/metrics.js
import { metrics, trace, context } from '@opentelemetry/api';
const meter = metrics.getMeter('mbp-s2');
export const canaryCounter = meter.createCounter('mbp.canary.decisions', {
  description: 'Decisões de roteamento: canary/stable',
});
export function recordDecision(decision, attrs={}){
  canaryCounter.add(1, { decision, ...attrs });
  try {
    const span = trace.getSpan(context.active());
    if (span) span.setAttribute('mbp.canary.decision', decision);
  } catch (_) {}
}
"""
    python_snippet = """
# telemetry_metrics.py
from opentelemetry import metrics, trace
from opentelemetry.metrics import get_meter

_meter = get_meter("mbp-s2")
_canary_counter = _meter.create_counter("mbp.canary.decisions")

def record_decision(decision: str, **attrs):
    try:
        _canary_counter.add(1, attributes={"decision": decision, **attrs})
        span = trace.get_current_span()
        if span: span.set_attribute("mbp.canary.decision", decision)
    except Exception:
        pass
"""
    quick_commands = (
        (
            "Node",
            "CANARY_DEBUG=true SHADOW_ENABLED=false node app.js &\n"
            "curl -H 'x-internal-user:true' -H 'x-user-id:42' http://localhost:8080/mbp/ping",
        ),
        (
            "Python",
            "CANARY_DEBUG=true SHADOW_ENABLED=false uvicorn main:app --port 8080 &\n"
            "curl -H 'x-internal-user:true' -H 'x-user-id:42' http://localhost:8080/mbp/ping",
        ),
    )
    promql = (
        "sum by (decision) (increase(mbp.canary.decisions[5m]))",
        "sum by (decision) (increase(mbp_canary_decisions[5m]))",
    )
    return TelemetryHook(
        description=description,
        node_snippet=node_snippet,
        python_snippet=python_snippet,
        quick_commands=quick_commands,
        promql=promql,
    )


def _typed_variants_defaults() -> TypedVariants:
    ts_snippet = """
// src/middleware/shadow.ts
import type { Request, Response, NextFunction } from 'express';
import fetch from 'node-fetch';

const SHADOW_ENABLED = process.env.SHADOW_ENABLED === 'true';
const SHADOW_TARGET  = process.env.SHADOW_TARGET || 'https://api.mbp-s2-shadow';

export function shadowMirror(req: Request, _res: Response, next: NextFunction) {
  try {
    if (!SHADOW_ENABLED || !req.path.startsWith('/mbp')) return next();
    const url = SHADOW_TARGET + req.originalUrl;
    const opts: any = { method: req.method, headers: { ...req.headers }, body: req.method === 'GET' ? undefined : (req as any).rawBody };
    (fetch as any)(url, opts).catch(() => {});
  } catch {}
  return next();
}

// src/rollout/canary.ts
import fs from 'fs';
import yaml from 'js-yaml';
import type { Request } from 'express';

type CanaryCfg = { canary?: { enabled?: boolean; percent?: number; audience?: 'internal'|'all' } };
function loadCanary(): CanaryCfg {
  try { return (yaml.load(fs.readFileSync('configs/rollout/mbp_canary.yml','utf8')) as CanaryCfg) || {}; }
  catch { return { canary: { enabled:false, percent:0, audience:'internal' } }; }
}
export function routeByCanary(req: Request): 'canary'|'stable' {
  const cfg = loadCanary();
  const c = cfg.canary || { enabled:false, percent:0, audience:'internal' };
  if (!c.enabled) return 'stable';
  const isInternal = (req.headers['x-internal-user'] === 'true');
  if ((c.audience || 'internal') === 'internal' && !isInternal) return 'stable';
  const p = Number(c.percent || 0);
  const key = (req.headers['x-user-id'] || req.ip || '0').toString();
  const bucket = [...key].reduce((a,c)=>a + c.charCodeAt(0),0) % 100;
  return bucket < p ? 'canary' : 'stable';
}
"""
    py_snippet = """
# rollout_canary_typed.py
from pydantic import BaseModel, Field, ValidationError
from typing import Literal
import yaml
from hashlib import sha1

class CanaryModel(BaseModel):
    enabled: bool = Field(default=False)
    percent: int = Field(default=0, ge=0, le=100)
    audience: Literal['internal','all'] = 'internal'

class RootCfg(BaseModel):
    canary: CanaryModel = CanaryModel()

def load_canary(path: str = 'configs/rollout/mbp_canary.yml') -> RootCfg:
    try:
        with open(path, 'r', encoding='utf-8') as fp:
            raw = yaml.safe_load(fp) or {}
        return RootCfg.model_validate(raw)
    except (FileNotFoundError, ValidationError):
        return RootCfg()

def route_by_canary_typed(headers, client_ip: str) -> str:
    cfg = load_canary()
    c = cfg.canary
    if not c.enabled:
        return 'stable'
    is_internal = str(headers.get('x-internal-user','')).lower() == 'true'
    if c.audience == 'internal' and not is_internal:
        return 'stable'
    key = headers.get('x-user-id') or client_ip or '0'
    bucket = int(sha1(key.encode()).hexdigest(), 16) % 100
    return 'canary' if bucket < c.percent else 'stable'
"""
    return TypedVariants(ts_snippet=ts_snippet, py_snippet=py_snippet)


def _liveness_note_defaults() -> LivenessNote:
    statement = (
        "Dado hashing determinístico por usuário, ao editar `percent: p1 → p2` no YAML e reiniciar o serviço, "
        "o sistema converge para uma fração estável ≈ `p2%` dos usuários internos roteados a `canary`."
    )
    conditions = (
        "Arquivo `configs/rollout/mbp_canary.yml` carregado na inicialização (ou hot-reload se implementado).",
        "O algoritmo de partição por usuário é puro e determinístico.",
    )
    steps = (
        "Edite o YAML para o novo valor: `percent: 10` (exemplo).",
        "Reinicie o serviço (ou acione reload). Em poucos segundos, as novas decisões passam a refletir `p2`.",
    )
    observations = (
        "> Com `CANARY_DEBUG=true`, logs mostrarão `percent` e `decision` em tempo real.",
        "> Em Prom, `increase(mbp_canary_decisions[5m])` refletirá o novo mix.",
    )
    return LivenessNote(
        statement=statement,
        conditions=conditions,
        steps=steps,
        observations=observations,
    )


def build_prompt_extras() -> str:
    """Render the optional extras bundle as Markdown."""

    sections: Iterable[str] = (
        _safety_proof_defaults().to_markdown(),
        _telemetry_defaults().to_markdown(),
        _typed_variants_defaults().to_markdown(),
        _liveness_note_defaults().to_markdown(),
    )
    return "\n\n---\n\n".join(sections)


__all__ = [
    "build_prompt_extras",
    "SafetyProofSketch",
    "TelemetryHook",
    "TypedVariants",
    "LivenessNote",
]

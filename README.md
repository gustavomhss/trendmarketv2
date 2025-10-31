# Sprint Playbook Pack — 10/10
Este pacote instala a espinha dorsal do seu Playbook de Sprint:

- Trio de YAMLs canônicos (DbC): `.sprint/deliverables.yml`, `.sprint/gates.yml`, `.sprint/filemap.yml`
- Schemas JSON: `.sprint/schemas/*.schema.yaml`
- Guard: `scripts/sprint_guard.py` — valida schemas, executa Gates, checa filemap, produz scorecard e evidências
- Storyboard: `scripts/render_storyboard.py` — gera `docs/Storyboard.md` a partir dos YAMLs
- CI: `.github/workflows/sprint-guard.yml` com `actions/checkout@11bd71901bbe5b1630ceea73d27597364c9af683` pinado

## Uso rápido
1) Copie tudo para a raiz do repositório.
2) Ajuste `.sprint/deliverables.yml`, `.sprint/gates.yml` e `.sprint/filemap.yml` para sua sprint atual.
3) Rode local: `python3 scripts/sprint_guard.py && python3 scripts/render_storyboard.py`
4) No GitHub, rode o workflow **Sprint Guard** em *Actions*.

A saída vai para `out/scorecards/sprint_guard_scorecard.json` e `out/evidence/`.

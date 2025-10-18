# Orçamento de Cardinalidade — Sprint 2

- **Teto global:** 12.000 séries.
- **Domínios:**
  - DEC ≤ 2.000
  - MBP ≤ 3.000
  - FE ≤ 2.000
  - DATA ≤ 2.000
  - INT ≤ 1.000
  - SEC ≤ 1.000

A verificação automatizada roda em `scripts/analysis/cardinality_report.sh`, que lê `seeds/load/cardinality_seed.json`, produz `cardinality.txt` e uma visão CSV/PNG com o status por domínio. Qualquer desvio gera `status=BREACH` e indica o excedente que deve ser apagado antes do próximo deploy.

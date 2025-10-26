# Q1 Boss Final

❌ Status global: **FAIL**

- Relatório gerado em: 2025-10-26T03:24:03Z
- Bundle SHA-256: `9d0914260ba82c82370f4dbc02cdde84f5f140ef9f577b4d3e52131c8a234f87`

| Stage | Status | Notas |
| --- | --- | --- |
| S1 | ❌ FAIL | primary:FAIL BOSS-E-S1-LINT:Ruff lint (exit 1) | clean:FAIL BOSS-E-S1-LINT:Ruff lint (exit 1) |
| S2 | ✅ PASS | primary:PASS PASS:S2 primary guard completado | clean:PASS PASS:S2 clean guard completado |
| S3 | ❌ FAIL | primary:FAIL BOSS-E-S3-SMOKE:Observability smoke (exit 2) | clean:FAIL BOSS-E-S3-SMOKE:Observability smoke (exit 2) |
| S4 | ❌ FAIL | primary:FAIL BOSS-E-S4-YAML:Comando ausente: yamllint | clean:FAIL BOSS-E-S4-YAML:Comando ausente: yamllint |
| S5 | ✅ PASS | primary:PASS PASS:S5 primary guard completado | clean:PASS PASS:S5 clean guard completado |
| S6 | ✅ PASS | primary:PASS PASS:S6 primary guard completado | clean:PASS PASS:S6 clean guard completado |

## Governança
- Cada estágio deve publicar bundles para `primary` e `clean`.
- O status global é FAIL se qualquer estágio falhar em qualquer variante.


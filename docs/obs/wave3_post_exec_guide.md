# Wave 3 — Pós-Execução (Checklist Detalhado)

Este guia explica, passo a passo, como finalizar a Wave 3 depois que os
workflows **CRD Epic — Plan** e **CRD Epic — Exec** (profile=`fast` e
`full`) ficarem verdes. Nenhum conhecimento prévio é necessário: siga cada etapa
na ordem para publicar a release com os artefatos exigidos pelo épico CRD-8.

## 1. Baixar o artefato `obs-bundle-*`
1. Abra a aba **Actions** do repositório no GitHub.
2. Clique no run mais recente e verde de **CRD Epic — Exec** com `profile=full`.
3. Na seção **Artifacts**, faça o download do arquivo `obs-bundle-*.zip`.

> **Dica:** mantenha o nome original do arquivo; ele é usado na publicação da
> release.

## 2. Descompactar e validar o bundle
1. Descompacte o `.zip` na raiz do repositório (o mesmo diretório que contém
   `scripts/` e `docs/`).
2. Confirme que a pasta `out/obs_gatecheck/` foi criada.
3. Abra `out/obs_gatecheck/summary.json` e verifique os campos:
   - `"acceptance": "OK"`
   - `"gatecheck": "OK"`
4. Abra `out/obs_gatecheck/logs/orr_all.txt`, role até o final e confirme que as
   linhas `ACCEPTANCE_OK` e `GATECHECK_OK` estão presentes.
5. Certifique-se de que `bundle.zip` e `bundle.sha256.txt` estão dentro de
   `out/obs_gatecheck/`.

Se qualquer item estiver ausente, o bundle não pode ser promovido — volte ao
workflow Exec e investigue a falha.

## 3. Gerar manifestos, metadata e release notes
Execute os comandos abaixo na raiz do repositório (o ambiente precisa ter
Python 3):

```bash
python3 scripts/obs_release_manifest.py
python3 scripts/obs_release_finalize.py
python3 scripts/obs_release_notes.py
```

Cada comando deve encerrar com `*_OK`. Eles criam/atualizam:

- `out/obs_gatecheck/release_manifest.json`
- `out/obs_gatecheck/release_metadata.json`
- `out/obs_gatecheck/release_notes.md`

## 4. Validar o bundle com `obs_bundle_report.py`
Rode o utilitário abaixo para gerar automaticamente o rodapé de evidências da
PR e um resumo da release:

```bash
python3 scripts/obs_bundle_report.py
```

A saída inclui:

- Confirmação de que acceptance/gatecheck estão `OK`.
- SHA256 do bundle e contagem de evidências.
- Valores de SLI (p95 swap, freshness, CDC lag, drift, hook coverage).
- Resumo de `release_metadata.json`.
- Trecho de `release_notes.md` pronto para ser usado na release.

Se o script acusar arquivos faltantes, corrija antes de prosseguir.

## 5. Completar `ops/release/promotion_checklist.md`
Abra o arquivo e marque todos os itens das seções **Pré-promoção**, **Promoção**
e **Pós-promoção**:

- Watchers A110 verdes e testados.
- Dashboards D1–D6 exportados.
- SBOM presente com hash.
- Custos/cardinalidade abaixo do orçamento.
- Evidências arquivadas por ≥ 30 dias.

## 6. Atualizar a Pull Request
Cole em um comentário (ou atualize a descrição da PR) com o rodapé emitido pelo
script `obs_bundle_report.py`, além de:

- Links dos runs Plan/Exec usados.
- Nome do artefato `obs-bundle-*` baixado.
- SHA256 copiado de `bundle.sha256.txt`.

Verifique que os checks obrigatórios `plan / plan` e `exec / orr` permanecem
verdes e que os CODEOWNERS relevantes aprovaram.

## 7. Fazer merge da PR
Com as aprovações em ordem e os checks verdes, utilize o botão de merge do
GitHub (sem push direto na branch default).

## 8. Publicar a release `crd-8-obs-YYYYMMDD`
1. Abra a aba **Releases** e clique em **Draft a new release**.
2. Use como tag `crd-8-obs-YYYYMMDD` (a data está em
   `out/obs_gatecheck/release_metadata.json` → campo `version`).
3. Faça upload de `obs-bundle-*.zip` e `bundle.sha256.txt`.
4. Copie o conteúdo de `out/obs_gatecheck/release_notes.md` para o corpo da
   release.
5. Publicar.

## 9. Arquivar e comunicar
- Armazene o bundle e os manifestos em local seguro (retenção mínima: 30 dias).
- Compartilhe os links da PR mergeada, da release publicada e o SHA256 com os
  stakeholders para fechar oficialmente a Wave 3.

Seguindo este roteiro, todas as exigências de promoção do épico CRD-8 ficam
cobertas sem passos implícitos ou comandos escondidos.

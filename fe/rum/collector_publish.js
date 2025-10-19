#!/usr/bin/env node
const fs = require('fs');
const path = require('path');

const outDir = path.join(__dirname, '..', '..', 'out', 's4_orr', 'EVI');
const snapshot = path.join(outDir, 'web_inp_snapshot.json');
const publish = path.join(outDir, 'rum_snapshot_manifest.json');

if (!fs.existsSync(snapshot)) {
  console.error('Snapshot RUM inexistente:', snapshot);
  process.exit(1);
}

const data = {
  artifact: path.relative(process.cwd(), snapshot),
  generated_at: new Date().toISOString(),
  metric: 'web_vitals_inp_ms',
};

fs.writeFileSync(publish, JSON.stringify(data, null, 2));
console.log('Manifest RUM salvo em', publish);

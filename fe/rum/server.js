#!/usr/bin/env node
const http = require('http');
const url = require('url');
const metrics = new Map();

function setMetric(page, env, value) {
  const key = `${page}|${env}`;
  metrics.set(key, { page, env, value });
}

function renderMetrics() {
  let body = '';
  for (const { page, env, value } of metrics.values()) {
    body += `web_vitals_inp_ms{page="${page}",env="${env}"} ${value}\n`;
  }
  return body;
}

const server = http.createServer((req, res) => {
  const { pathname } = url.parse(req.url);
  if (pathname === '/collect' && req.method === 'POST') {
    let body = '';
    req.on('data', chunk => {
      body += chunk;
    });
    req.on('end', () => {
      try {
        const data = JSON.parse(body);
        setMetric(data.page, data.env, data.value);
        res.writeHead(204);
        res.end();
      } catch (err) {
        res.writeHead(400);
        res.end('invalid payload');
      }
    });
  } else if (pathname === '/metrics') {
    res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8' });
    res.end(renderMetrics());
  } else {
    res.writeHead(404);
    res.end('not found');
  }
});

const port = process.env.RUM_PORT || 9314;
server.listen(port, () => {
  console.log(`RUM collector listening on ${port}`);
});

#!/usr/bin/env node
"use strict";

const http = require("http");

const HOST = "127.0.0.1";
const PORT = parseInt(process.env.PORT || "8080", 10);
const HEALTH_PATH = process.env.HEALTH_PATH || "/health";

const server = http.createServer((req, res) => {
  if (req.method === "GET" && req.url === HEALTH_PATH) {
    res.writeHead(200, { "Content-Type": "application/json" });
    res.end(JSON.stringify({ status: "ok" }));
    return;
  }

  res.writeHead(404, { "Content-Type": "application/json" });
  res.end(JSON.stringify({ error: "not_found" }));
});

server.listen(PORT, HOST, () => {
  console.log(`[sut-server] listening on http://${HOST}:${PORT}${HEALTH_PATH}`);
});

const shutdown = (signal) => {
  console.log(`[sut-server] received ${signal}, shutting down`);
  server.close(() => {
    process.exit(0);
  });
};

process.on("SIGINT", () => shutdown("SIGINT"));
process.on("SIGTERM", () => shutdown("SIGTERM"));

#!/usr/bin/env python3
"""Minimal HTTP server exposing /health endpoint."""

from http.server import BaseHTTPRequestHandler, HTTPServer
import json


class HealthHandler(BaseHTTPRequestHandler):
    server_version = "sut-health/1.0"

    def log_message(self, format: str, *args) -> None:  # type: ignore[override]
        return

    def do_GET(self) -> None:  # type: ignore[override]
        if self.path == "/health":
            body = json.dumps({"status": "ok"}).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        self.send_response(404)
        self.end_headers()


def main() -> None:
    server = HTTPServer(("0.0.0.0", 8080), HealthHandler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path


def get_json(url: str, timeout: int = 60) -> dict:
    request = urllib.request.Request(url, headers={"Accept": "application/json"})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return json.load(response)


def api_url(base: str, path: str) -> str:
    return f"{base.rstrip('/')}/{path.lstrip('/')}"


def wait_ready(base: str, timeout_seconds: int) -> list[str]:
    deadline = time.time() + timeout_seconds
    last_error: Exception | None = None
    while time.time() < deadline:
        try:
            payload = get_json(api_url(base, "api/services"), timeout=10)
            services = payload.get("data") or []
            if isinstance(services, list):
                return [str(service) for service in services]
        except Exception as exc:  # readiness polling is intentionally broad
            last_error = exc
        time.sleep(2)
    raise RuntimeError(f"Jaeger API did not become ready: {last_error}")


def choose_service(services: list[str], requested: str) -> str:
    if requested in services:
        return requested
    normalized = requested.lower().replace("_", "-")
    matches = [
        service for service in services
        if normalized in service.lower().replace("_", "-")
    ]
    if len(matches) == 1:
        return matches[0]
    if not matches:
        checkout = [service for service in services if "checkout" in service.lower()]
        if len(checkout) == 1:
            return checkout[0]
    raise RuntimeError(
        f"could not resolve service {requested!r}; available services: {services}"
    )


def fetch(base: str, service: str, start_us: int, end_us: int, limit: int) -> dict:
    query = urllib.parse.urlencode({
        "service": service,
        "start": start_us,
        "end": end_us,
        "limit": limit,
        "lookback": "custom",
    })
    return get_json(api_url(base, f"api/traces?{query}"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--base", default="http://localhost:8080/jaeger")
    parser.add_argument("--service", default="checkout")
    parser.add_argument("--start-us", type=int)
    parser.add_argument("--end-us", type=int)
    parser.add_argument("--seconds", type=int, default=60)
    parser.add_argument("--limit", type=int, default=5000)
    parser.add_argument("--ready-timeout", type=int, default=180)
    args = parser.parse_args()

    services = wait_ready(args.base, args.ready_timeout)
    service = choose_service(services, args.service)
    end_us = args.end_us or int(time.time() * 1_000_000)
    start_us = args.start_us or end_us - args.seconds * 1_000_000
    payload = fetch(args.base, service, start_us, end_us, args.limit)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload), encoding="utf-8")
    traces = [item for item in payload.get("data", []) if item.get("spans")]
    print(json.dumps({
        "output": str(args.output),
        "traces": len(traces),
        "service": service,
        "available_services": services,
        "start_us": start_us,
        "end_us": end_us,
    }))


if __name__ == "__main__":
    main()

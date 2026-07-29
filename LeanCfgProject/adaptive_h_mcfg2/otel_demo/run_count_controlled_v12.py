#!/usr/bin/env python3
"""Collect one count-controlled OpenTelemetry Demo checkout trace per run.

External experiment label: ADP MCFG v5.  Internal protocol version: V12,
because it follows the repository's V11 real-trace experiment.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
import uuid
from pathlib import Path
from typing import Any

PRODUCT_IDS = (
    "0PUK6V6EV0",
    "1YMWWN1N4O",
    "2ZYFJ3GM2N",
    "66VCHSJNUP",
    "6E92ZMYYFZ",
    "9SIQT8TOJO",
    "HQTGWGPNH4",
    "L9ECAV7KIM",
    "LS4PSXUNUM",
    "OLJCESPC7Z",
)


def run(command: list[str], cwd: Path, *, check: bool = True) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=check)


def capture(command: list[str], cwd: Path) -> str:
    try:
        return subprocess.check_output(
            command, cwd=cwd, text=True, stderr=subprocess.STDOUT
        ).strip()
    except Exception:
        return "unknown"


def resolve_load_generator(compose: list[str], root: Path) -> str | None:
    raw = capture([*compose, "config", "--services"], root)
    if raw == "unknown":
        return None
    services = [line.strip() for line in raw.splitlines() if line.strip()]
    for exact in ("load-generator", "loadgenerator", "loadgen"):
        if exact in services:
            return exact
    matches = [service for service in services if "load" in service.lower()]
    return matches[0] if len(matches) == 1 else None


def post_json(url: str, payload: dict[str, Any], timeout: int = 60) -> tuple[int, str]:
    data = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=data,
        headers={"Content-Type": "application/json", "Accept": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            return int(response.status), response.read().decode("utf-8", errors="replace")
    except urllib.error.HTTPError as exc:
        body = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"POST {url} failed with HTTP {exc.code}: {body}") from exc


def wait_frontend(base: str, timeout_seconds: int) -> None:
    deadline = time.time() + timeout_seconds
    last_error: Exception | None = None
    while time.time() < deadline:
        try:
            request = urllib.request.Request(base.rstrip("/") + "/", method="GET")
            with urllib.request.urlopen(request, timeout=10) as response:
                if int(response.status) < 500:
                    return
        except Exception as exc:
            last_error = exc
        time.sleep(2)
    raise RuntimeError(f"frontend did not become ready: {last_error}")


def checkout_payload(user_id: str) -> dict[str, Any]:
    return {
        "userId": user_id,
        "email": "count-controlled@example.com",
        "address": {
            "streetAddress": "1 Projection Way",
            "city": "Trace City",
            "state": "CA",
            "country": "United States",
            "zipCode": "94016",
        },
        "userCurrency": "USD",
        "creditCard": {
            "creditCardNumber": "4432-8015-6152-0454",
            "creditCardCvv": 672,
            "creditCardExpirationYear": 2030,
            "creditCardExpirationMonth": 1,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("demo_root", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v12-count-runs"))
    parser.add_argument("--min-count", type=int, default=1)
    parser.add_argument("--max-count", type=int, default=10)
    parser.add_argument("--replicas", type=int, default=5)
    parser.add_argument("--warmup-seconds", type=int, default=45)
    parser.add_argument("--flush-seconds", type=int, default=5)
    parser.add_argument("--ready-timeout", type=int, default=240)
    parser.add_argument("--frontend-base", default="http://localhost:8080")
    parser.add_argument("--jaeger-base", default="http://localhost:8080/jaeger/ui")
    parser.add_argument("--service", default="checkout")
    parser.add_argument("--compose-file", action="append", default=[])
    parser.add_argument("--keep-running", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    if args.min_count < 1 or args.max_count < args.min_count:
        raise SystemExit("invalid count range")
    if args.max_count > len(PRODUCT_IDS):
        raise SystemExit(
            f"max-count {args.max_count} exceeds the {len(PRODUCT_IDS)} fixed product IDs"
        )
    if args.replicas < 1:
        raise SystemExit("replicas must be positive")

    root = args.demo_root.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    tools = Path(__file__).resolve().parent
    if shutil.which("docker") is None and not args.dry_run:
        raise SystemExit("docker was not found")

    compose_files = list(args.compose_file) or ["compose.yaml"]
    compose = ["docker", "compose"]
    for name in compose_files:
        compose.extend(["-f", name])
    up = [*compose, "up", "--force-recreate", "--remove-orphans", "--detach"]
    down = [*compose, "down", "--remove-orphans"]

    manifest: dict[str, Any] = {
        "protocol": "ADP-MCFG-v5 / internal V12 count-controlled collection",
        "demo_root": str(root),
        "git_commit": capture(["git", "rev-parse", "HEAD"], root),
        "git_status": capture(["git", "status", "--short"], root),
        "docker_version": capture(
            ["docker", "version", "--format", "{{.Server.Version}}"], root
        ),
        "compose_version": capture(["docker", "compose", "version"], root),
        "compose_files": compose_files,
        "frontend_base": args.frontend_base,
        "jaeger_base": args.jaeger_base,
        "requested_service": args.service,
        "count_range": [args.min_count, args.max_count],
        "replicas": args.replicas,
        "product_ids": list(PRODUCT_IDS),
        "load_generator_service": None,
        "runs": [],
    }

    if args.dry_run:
        planned = [
            f"run-c{count:02d}-r{replica:02d}"
            for count in range(args.min_count, args.max_count + 1)
            for replica in range(args.replicas)
        ]
        print(json.dumps({"up": up, "down": down, "planned_runs": planned, "manifest": manifest}, indent=2))
        return

    run(up, root)
    try:
        load_generator = resolve_load_generator(compose, root)
        manifest["load_generator_service"] = load_generator
        if load_generator:
            # Ambient traffic would destroy the one-transaction-per-run invariant.
            run([*compose, "stop", load_generator], root)
        wait_frontend(args.frontend_base, args.ready_timeout)
        time.sleep(args.warmup_seconds)

        for count in range(args.min_count, args.max_count + 1):
            for replica in range(args.replicas):
                run_id = f"run-c{count:02d}-r{replica:02d}"
                target = output / f"{run_id}.json"
                user_id = str(uuid.uuid5(uuid.NAMESPACE_URL, f"adp-mcfg-v12:{run_id}"))
                products = PRODUCT_IDS[:count]
                request_log: list[dict[str, Any]] = []

                # Start the Jaeger window before issuing the controlled transaction.
                started = int(time.time() * 1_000_000) - 2_000_000
                for product_id in products:
                    status, body = post_json(
                        args.frontend_base.rstrip("/") + "/api/cart",
                        {
                            "item": {"productId": product_id, "quantity": 1},
                            "userId": user_id,
                        },
                    )
                    request_log.append(
                        {
                            "endpoint": "/api/cart",
                            "product_id": product_id,
                            "status": status,
                            "response_prefix": body[:300],
                        }
                    )
                status, body = post_json(
                    args.frontend_base.rstrip("/") + "/api/checkout",
                    checkout_payload(user_id),
                )
                request_log.append(
                    {
                        "endpoint": "/api/checkout",
                        "status": status,
                        "response_prefix": body[:1000],
                    }
                )
                time.sleep(args.flush_seconds)
                ended = int(time.time() * 1_000_000) + 2_000_000
                command = [
                    sys.executable,
                    str(tools / "collect_jaeger_v11.py"),
                    str(target),
                    "--base",
                    args.jaeger_base,
                    "--service",
                    args.service,
                    "--start-us",
                    str(started),
                    "--end-us",
                    str(ended),
                ]
                run(command, root)
                manifest["runs"].append(
                    {
                        "run_id": run_id,
                        "path": str(target),
                        "expected_item_count": count,
                        "replica": replica,
                        "user_id": user_id,
                        "product_ids": list(products),
                        "start_us": started,
                        "end_us": ended,
                        "requests": request_log,
                    }
                )
                (output / "manifest.json").write_text(
                    json.dumps(manifest, indent=2), encoding="utf-8"
                )
    finally:
        (output / "docker-compose-ps.txt").write_text(
            capture([*compose, "ps", "-a"], root), encoding="utf-8"
        )
        (output / "docker-compose-logs.txt").write_text(
            capture([*compose, "logs", "--no-color", "--tail", "5000"], root),
            encoding="utf-8",
        )
        if not args.keep_running:
            run(down, root, check=False)


if __name__ == "__main__":
    main()

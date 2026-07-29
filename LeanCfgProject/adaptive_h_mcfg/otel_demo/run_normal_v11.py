#!/usr/bin/env python3
"""Collect unmodified OpenTelemetry Demo traces with reproducibility metadata."""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path


def run(command: list[str], cwd: Path) -> None:
    print("+", " ".join(command), flush=True)
    subprocess.run(command, cwd=cwd, check=True)


def capture(command: list[str], cwd: Path) -> str:
    try:
        return subprocess.check_output(command, cwd=cwd, text=True, stderr=subprocess.STDOUT).strip()
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("demo_root", type=Path)
    parser.add_argument("--output", type=Path, default=Path("mcfg-v11-normal-runs"))
    parser.add_argument("--runs", type=int, default=5)
    parser.add_argument("--warmup-seconds", type=int, default=45)
    parser.add_argument("--collect-seconds", type=int, default=90)
    parser.add_argument("--jaeger-base", default="http://localhost:8080/jaeger")
    parser.add_argument("--service", default="checkout")
    parser.add_argument("--compose-file", action="append", default=[])
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--keep-running", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    root = args.demo_root.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    tools = Path(__file__).resolve().parent
    if shutil.which("docker") is None and not args.dry_run:
        raise SystemExit("docker was not found")

    compose_files = list(args.compose_file)
    if not compose_files:
        minimal_candidates = ["docker-compose.minimal.yml", "compose.minimal.yaml"]
        if args.minimal:
            selected = next((name for name in minimal_candidates if (root / name).exists()), None)
            if selected is None:
                raise SystemExit("minimal Compose file was not found")
            compose_files = [selected]
        else:
            selected = next((name for name in ("compose.yaml", "docker-compose.yaml") if (root / name).exists()), None)
            if selected is None and not args.dry_run:
                raise SystemExit("compose.yaml was not found")
            compose_files = [selected or "compose.yaml"]

    compose = ["docker", "compose"]
    for name in compose_files:
        compose.extend(["-f", name])
    up = compose + ["up", "--force-recreate", "--remove-orphans", "--detach"]
    down = compose + ["down", "--remove-orphans"]

    load_generator_service = None if args.dry_run else resolve_load_generator(compose, root)
    manifest: dict[str, object] = {
        "demo_root": str(root),
        "git_commit": capture(["git", "rev-parse", "HEAD"], root),
        "git_status": capture(["git", "status", "--short"], root),
        "docker_version": capture(["docker", "version", "--format", "{{.Server.Version}}"], root),
        "compose_version": capture(["docker", "compose", "version"], root),
        "compose_files": compose_files,
        "jaeger_base": args.jaeger_base,
        "requested_service": args.service,
        "load_generator_service": load_generator_service,
        "runs": [],
    }

    if args.dry_run:
        print(json.dumps({"up": up, "down": down, "manifest": manifest}, indent=2))
        return

    run(up, root)
    try:
        for index in range(args.runs):
            target = output / f"run-{index:02d}.json"
            # Restarting the load generator gives each collection window a clear
            # run boundary while the application and Jaeger remain warm.
            if load_generator_service:
                subprocess.run(compose + ["restart", load_generator_service], cwd=root, check=False)
            time.sleep(args.warmup_seconds)
            started = int(time.time() * 1_000_000)
            time.sleep(args.collect_seconds)
            ended = int(time.time() * 1_000_000)
            command = [
                sys.executable,
                str(tools / "collect_jaeger_v11.py"),
                str(target),
                "--base", args.jaeger_base,
                "--service", args.service,
                "--start-us", str(started),
                "--end-us", str(ended),
            ]
            run(command, root)
            manifest["runs"].append({
                "run": index,
                "path": str(target),
                "start_us": started,
                "end_us": ended,
            })
            (output / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    finally:
        # Preserve container state and logs before teardown.  This is especially
        # useful on ephemeral GitHub-hosted runners, where the VM disappears
        # after the workflow finishes.
        (output / "docker-compose-ps.txt").write_text(
            capture([*compose, "ps", "-a"], root), encoding="utf-8"
        )
        (output / "docker-compose-logs.txt").write_text(
            capture([*compose, "logs", "--no-color", "--tail", "3000"], root),
            encoding="utf-8",
        )
        if not args.keep_running:
            run(down, root)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Run every finite and infinite certificate using only Python programs."""
from __future__ import annotations

from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def run(*arguments: str) -> None:
    command = [sys.executable, *arguments]
    print('+', ' '.join(command), flush=True)
    subprocess.run(command, cwd=BASE, check=True)


def main() -> None:
    run('finite_check.py', '--bits', '14')
    run('regression_check.py')
    run('build_graphs.py')
    run('verify_antichain.py')
    print('ALL PYTHON CERTIFICATES PASSED')


if __name__ == '__main__':
    main()

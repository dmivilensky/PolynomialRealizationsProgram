#!/usr/bin/env bash
# Public entry point; all generated data live in artifacts, dependencies outside krylov-code.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python_bin="${XR_PYTHON:-/tmp/clc-xr-venv/bin/python}"
[[ -x "$python_bin" ]] || { printf 'Set XR_PYTHON to an external Python environment; see README.md.\n' >&2; exit 1; }
export PYTHONPATH="$project_dir/src${PYTHONPATH:+:$PYTHONPATH}"
export PYTHONDONTWRITEBYTECODE=1
# shellcheck disable=SC1091
source "$project_dir/env.sh"
cd "$project_dir"
if [[ $# -eq 0 || "$1" == --* ]]; then set -- run "$@"; fi
if [[ "$1" == run || "$1" == resume ]]; then
    lock="$project_dir/artifacts/logs/runner.lock"
    mkdir -p "$(dirname -- "$lock")"
    if ! mkdir "$lock" 2>/dev/null; then
        owner="$(cat "$lock/pid" 2>/dev/null || true)"
        if [[ "$owner" =~ ^[0-9]+$ ]] && ! kill -0 "$owner" 2>/dev/null; then
            rm -f "$lock/pid"
            rmdir "$lock"
            mkdir "$lock"
        else
            printf 'Another runner owns %s (PID %s).\n' "$lock" "$owner" >&2
            exit 1
        fi
    fi
    printf '%s\n' "$$" > "$lock/pid"
    trap 'rm -f "$lock/pid"; rmdir "$lock"' EXIT
    "$python_bin" -B -u -m xrbench "$@"
else
    exec "$python_bin" -B -u -m xrbench "$@"
fi

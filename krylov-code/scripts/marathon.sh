#!/usr/bin/env bash
# Detached, logged entry point. start and resume use the same validated runner.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python_bin="${XR_PYTHON:-/tmp/clc-xr-venv/bin/python}"
session="${XR_SCREEN_SESSION:-krylov-experiments}"
output="${XR_MARATHON_OUTPUT:-$project_dir/artifacts/run}"
[[ -x "$python_bin" ]] || { printf 'Set XR_PYTHON to the external environment.\n' >&2; exit 1; }
export PYTHONPATH="$project_dir/src${PYTHONPATH:+:$PYTHONPATH}"
export PYTHONDONTWRITEBYTECODE=1
# shellcheck disable=SC1091
source "$project_dir/env.sh"
mkdir -p "$output/logs"
case "${1:-status}" in
  start|resume)
    # macOS screen may return 1 even while listing live sockets. Inspect its
    # output independently of that exit status under pipefail.
    active_screens="$(screen -ls 2>/dev/null || true)"
    if grep -F ".$session" <<< "$active_screens" >/dev/null; then
      printf 'Screen session already active: %s\n' "$session" >&2
      exit 1
    fi
    # Lowercase -dm forks the detached server; -Dm keeps the launcher waiting.
    screen -dmS "$session" bash "$project_dir/scripts/marathon.sh" _run
    printf 'Started %s; log: %s/logs/marathon.log\n' "$session" "$output"
    ;;
  _run)
    exec > >(tee -a "$output/logs/marathon.log") 2>&1
    exec "$python_bin" -B -u "$project_dir/scripts/marathon.py" run --output "$output"
    ;;
  status)
    "$python_bin" -B "$project_dir/scripts/marathon.py" status --output "$output"
    ;;
  attach) exec screen -r "$session" ;;
  stop)
    "$python_bin" -B "$project_dir/scripts/marathon.py" stop --output "$output"
    screen -S "$session" -X quit >/dev/null 2>&1 || true
    ;;
  *) printf 'Usage: %s {start|resume|status|attach|stop}\n' "$0" >&2; exit 2 ;;
esac

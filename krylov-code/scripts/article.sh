#!/usr/bin/env bash
# Rendering reads the frozen manifest/history and never evaluates a problem.
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec bash "$project_dir/scripts/run.sh" render "$@"

#!/bin/sh
set -eu
package_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$package_dir"
export MPLCONFIGDIR="${MPLCONFIGDIR:-${TMPDIR:-/tmp}/bezout-matplotlib}"
export XDG_CACHE_HOME="${XDG_CACHE_HOME:-${TMPDIR:-/tmp}/bezout-cache}"
export PYTHONDONTWRITEBYTECODE=1
if [ -x .venv/bin/python ]; then python_bin=.venv/bin/python; else python_bin=python3; fi
exec "$python_bin" run_all.py "$@"

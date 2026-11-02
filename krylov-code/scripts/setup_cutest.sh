#!/usr/bin/env bash
# Build pinned native dependencies outside krylov-code. No downloads occur with --check.
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
python_bin="${XR_PYTHON:-/tmp/clc-xr-venv/bin/python}"
native_dir="${XR_NATIVE_DIR:-/tmp/clc-xr-native}"
cutest_commit=7dafe08040f83a53712a52f675e02a47b153f0a8
sifdecode_commit=f39612293718df0bfcb96289e2f1233a041dcf90
mastsif_commit=319d16b35f711ffd2e8dbf8a7fc4b6708fa536e9
mode="${1:---help}"

usage() {
    cat <<'HELP'
Usage: bash scripts/setup_cutest.sh --check | --install

  --check    Check paths, toolchain and Python packages; no downloads or builds.
  --install  Fetch pinned sources, build/test CUTEst and SIFDecode, install
             PyCUTEst 1.8.2, then compile one ROSENBR interface as a smoke test.

Environment:
  XR_NATIVE_DIR  External native cache (default /tmp/clc-xr-native).
  XR_PYTHON      Existing environment Python (default /tmp/clc-xr-venv/bin/python).
  XR_BUILD_JOBS  Build parallelism (default 4).
  CC, CXX, FC    Compiler executable overrides; GNU gfortran is required on PATH.

The interpreter and native cache must live outside the XR repository.
Run installation before a campaign, never concurrently with CUTEst workers.
See docs/NativeSetup.md for prerequisites and exact source revisions.
HELP
}

fail() { printf 'CUTEst setup: %s\n' "$*" >&2; exit 1; }
[[ $# -le 1 ]] || { usage >&2; exit 2; }
case "$mode" in
    --help|-h) usage; exit 0 ;;
    --check|--install) ;;
    *) usage >&2; exit 2 ;;
esac
[[ -x "$python_bin" ]] || fail "Python unavailable: $python_bin; create an external venv or set XR_PYTHON."

# Canonicalization also detects /tmp symlinks and paths back into the checkout.
native_dir="$("$python_bin" -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).expanduser().resolve())' "$native_dir")"
python_path="$("$python_bin" -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).absolute())' "$python_bin")"
case "$native_dir/" in "$project_dir/"*) fail "XR_NATIVE_DIR must be outside $project_dir" ;; esac
case "$python_path/" in "$project_dir/"*) fail "XR_PYTHON must be an external environment" ;; esac
export XR_NATIVE_DIR="$native_dir"
# env.sh honors external locations, compiler overrides and the platform SDK.
# The file path is computed from this script's directory.
# shellcheck disable=SC1091
source "$project_dir/env.sh"
export FC="${FC:-gfortran}"
export CC="${CC:-cc}"
export CXX="${CXX:-c++}"
python_dir="$(dirname -- "$python_bin")"
export PATH="$python_dir:$PATH"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPATH="$project_dir/src${PYTHONPATH:+:$PYTHONPATH}"

check_tools() {
    case "$(uname -s)" in Darwin|Linux) ;; *) fail 'PyCUTEst supports Linux and macOS.' ;; esac
    for tool in git ar gfortran "$CC" "$FC"; do
        command -v "$tool" >/dev/null || fail "Missing executable: $tool"
    done
    if [[ "$(uname -s)" == Darwin ]]; then
        command -v brew >/dev/null || fail 'PyCUTEst 1.8.2 requires Homebrew GCC on macOS.'
        command -v xcrun >/dev/null || fail 'Install Xcode Command Line Tools on macOS.'
        xcrun --find clang >/dev/null
        xcrun --sdk macosx --show-sdk-path >/dev/null
    fi
    "$python_bin" - <<'PY'
import sys
from pathlib import Path
import sysconfig
if sys.version_info < (3, 11):
    raise SystemExit('Python 3.11 or later is required')
header = Path(sysconfig.get_path('include')) / 'Python.h'
if not header.is_file():
    raise SystemExit(f'Python development headers missing: {header}')
print(f'Python: {sys.executable}')
PY
}

check_install() {
    [[ -f "$CUTEST/include/cutest.h" ]] || fail "Missing $CUTEST/include/cutest.h"
    [[ -f "$CUTEST/lib/libcutest_double.a" ]] || fail "Missing static double CUTEst library"
    [[ -x "$SIFDECODE/bin/sifdecoder" ]] || fail "Missing $SIFDECODE/bin/sifdecoder"
    [[ -f "$MASTSIF/CLASSF.DB" ]] || fail "Missing MASTSIF classification database"
    "$python_bin" - "$project_dir/src/xrbench/problems/cutest.json" <<'PY'
import importlib.metadata as md
import json
import os
from pathlib import Path
import sys
for name in ('numpy', 'setuptools', 'pycutest'):
    try:
        version = md.version(name)
    except md.PackageNotFoundError:
        raise SystemExit(f'Missing Python package: {name}')
    print(f'{name}: {version}')
    if name == 'pycutest' and version != '1.8.2':
        raise SystemExit('Expected pycutest==1.8.2')
root = Path(os.environ['MASTSIF'])
names = {r['name'] for r in json.loads(Path(sys.argv[1]).read_text())['problems']}
missing = sorted(n for n in names | {'ROSENBR'} if not (root / f'{n}.SIF').is_file())
if missing:
    raise SystemExit('Missing SIF problems: ' + ', '.join(missing))
print(f'SIF input files: {len(names)} frozen families plus ROSENBR smoke test')
PY
    for entry in "CUTEst:$cutest_commit" "SIFDecode:$sifdecode_commit" "mastsif:$mastsif_commit"; do
        name="${entry%%:*}"
        expected="${entry#*:}"
        if [[ -d "$native_dir/src/$name/.git" ]]; then
            actual="$(git -C "$native_dir/src/$name" rev-parse HEAD)"
            [[ "$actual" == "$expected" ]] || fail "$name source revision differs: $actual"
            printf '%s: %s\n' "$name" "$actual"
        fi
    done
    printf 'Native installation ready; --check did not compile or decode a problem.\n'
}

check_tools
if [[ "$mode" == --check ]]; then
    check_install
    exit 0
fi

jobs="${XR_BUILD_JOBS:-4}"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || fail 'XR_BUILD_JOBS must be a positive integer.'
"$python_bin" - "$project_dir" "$native_dir" <<'PY'
from pathlib import Path
import os
import sys
repository, native = map(lambda p: Path(p).resolve(), sys.argv[1:])
for key in ('CUTEST', 'SIFDECODE', 'MASTSIF', 'PYCUTEST_CACHE'):
    value = Path(os.environ[key]).resolve()
    if not value.is_relative_to(native) or value.is_relative_to(repository):
        raise SystemExit(f'{key}={value} is outside XR_NATIVE_DIR; unset explicit paths before --install')
PY

# Refuse concurrent installation into the same external tree. No force reset or
# deletion of an existing source checkout is performed by this script.
mkdir -p "$native_dir"
lock="$native_dir/.xr-install.lock"
mkdir "$lock" 2>/dev/null || fail "Another install owns $lock; verify it has stopped before removing this lock."
trap 'rmdir "$lock" 2>/dev/null || true' EXIT
mkdir -p "$native_dir/src" "$native_dir/build" "$native_dir/logs" "$PYCUTEST_CACHE"
exec > >(tee -a "$native_dir/logs/setup.log") 2>&1

# Keep every generated Python build/download artifact outside the repository.
export TMPDIR="$native_dir/build/tmp"
export PIP_CACHE_DIR="$native_dir/downloads/pip"
mkdir -p "$TMPDIR" "$PIP_CACHE_DIR"
"$python_bin" -m pip install 'meson==1.12.1' 'ninja==1.13.2' 'pycutest==1.8.2' 'setuptools>=68'

checkout() {
    local name="$1" url="$2" commit="$3" path="$native_dir/src/$1"
    if [[ -d "$path/.git" ]]; then
        [[ "$(git -C "$path" rev-parse HEAD)" == "$commit" ]] || fail "$name has a different revision; use a fresh XR_NATIVE_DIR."
        git -C "$path" diff --quiet || fail "$name has tracked local modifications."
        git -C "$path" diff --cached --quiet || fail "$name has staged modifications."
        return
    fi
    [[ ! -e "$path" ]] || fail "Refusing to overwrite non-git source directory $path"
    git init -q "$path"
    git -C "$path" remote add origin "$url"
    if [[ "$name" == mastsif ]]; then
        # A partial sparse clone obtains only this frozen study's SIF files;
        # the full MASTSIF data collection need not consume gigabytes locally.
        git -C "$path" sparse-checkout init --no-cone
        "$python_bin" - "$project_dir/src/xrbench/problems/cutest.json" > "$native_dir/logs/sif-paths.txt" <<'PY'
import json
from pathlib import Path
import sys
names = {r['name'] for r in json.loads(Path(sys.argv[1]).read_text())['problems']}
for name in sorted(names | {'ROSENBR'}):
    if not name.replace('_', '').isalnum():
        raise SystemExit(f'Invalid SIF name: {name}')
    print(f'/{name}.SIF')
for name in ('CLASSF.DB', 'README', 'README.md', 'LICENSE'):
    print('/' + name)
PY
        git -C "$path" sparse-checkout set --no-cone --stdin < "$native_dir/logs/sif-paths.txt"
    fi
    git -C "$path" fetch --depth=1 --filter=blob:none origin "$commit"
    git -C "$path" -c advice.detachedHead=false checkout --detach "$commit"
}

checkout CUTEst https://github.com/ralna/CUTEst.git "$cutest_commit"
checkout SIFDecode https://github.com/ralna/SIFDecode.git "$sifdecode_commit"
checkout mastsif https://github.com/ralna/SIF.git "$mastsif_commit"

build_meson() {
    local name="$1" prefix="$2" build="$native_dir/build/$1"
    shift 2
    if [[ -f "$build/meson-private/coredata.dat" ]]; then
        "$python_bin" -m mesonbuild.mesonmain setup --reconfigure "$build" "$native_dir/src/$name" \
            --prefix="$prefix" --libdir=lib --buildtype=release -Ddefault_library=static -Db_staticpic=true "$@"
    else
        "$python_bin" -m mesonbuild.mesonmain setup "$build" "$native_dir/src/$name" \
            --prefix="$prefix" --libdir=lib --buildtype=release -Ddefault_library=static -Db_staticpic=true "$@"
    fi
    "$python_bin" -m mesonbuild.mesonmain compile -C "$build" -j "$jobs"
    "$python_bin" -m mesonbuild.mesonmain install -C "$build"
}

# PyCUTEst 1.8.2 expects a PIC static double library and 32-bit Fortran integers.
build_meson CUTEst "$CUTEST" -Dtests=true -Dquadruple=false -Dint64=false
"$python_bin" -m mesonbuild.mesonmain test -C "$native_dir/build/CUTEst" --print-errorlogs
build_meson SIFDecode "$SIFDECODE"
check_install

"$python_bin" - <<'PY'
import numpy as np
import pycutest
p = pycutest.import_problem('ROSENBR')
x = np.asarray(p.x0, dtype=float)
f = float(p.obj(x))
g = np.asarray(p.grad(x), dtype=float)
assert p.n == 2 and np.isfinite(f) and np.all(np.isfinite(g))
print(f'Native ROSENBR smoke test: n={p.n}, f(x0)={f:g}, ||g(x0)||={np.linalg.norm(g):.8g}')
PY
"$python_bin" - "$native_dir" "$cutest_commit" "$sifdecode_commit" "$mastsif_commit" <<'PY'
import importlib.metadata as md
import json
from pathlib import Path
import platform
import sys
root = Path(sys.argv[1])
record = dict(CUTEst=sys.argv[2], SIFDecode=sys.argv[3], MASTSIF=sys.argv[4],
              python=sys.version, platform=platform.platform(),
              packages={p: md.version(p) for p in ('numpy', 'pycutest', 'meson', 'ninja')})
(root / 'native-build.json').write_text(json.dumps(record, indent=2) + '\n')
PY
printf 'Installation complete. Source env.sh before running the study.\n'

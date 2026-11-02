# Krylov optimization experiments

This directory contains the XR and XR-F solvers, benchmark adapters, numerical
comparisons, and generators for the figures and tables in `krylov.tex`.
It belongs to the enclosing repository alongside the Lean development in
[`krylov`](../krylov/).

## Installation

Use Python 3.13 for the dependencies in `requirements.txt`. Native solvers
require a C11 compiler and Python development headers. CUTEst additionally
requires GNU Fortran, Git and the platform build tools; see
[NativeSetup.md](docs/NativeSetup.md).

From the enclosing repository:

```sh
cd krylov-code
python3.13 -m venv /tmp/clc-xr-venv
export XR_PYTHON=/tmp/clc-xr-venv/bin/python
"$XR_PYTHON" -m pip install -r requirements.txt
bash scripts/setup_cutest.sh --install
bash scripts/setup_cutest.sh --check
```

Python environments, CUTEst installations, decoded problems, native binaries
and LIBSVM arrays use external caches. Set `XR_NATIVE_DIR`, `XR_KERNEL_CACHE`
and `XR_LIBSVM_DATA` to choose persistent locations outside this directory.
`XR_PYTHON` selects the interpreter used by the shell entry points.

## Run the experiments

```sh
bash scripts/marathon.sh start
bash scripts/marathon.sh status
bash scripts/marathon.sh attach
bash scripts/marathon.sh stop
bash scripts/marathon.sh resume
```

The runner prepares LIBSVM data, executes the main comparisons, settings,
reference and local studies, renders their results, validates the inputs and
copies the article assets into `artifacts/paper`. It runs one solver at a time
with one BLAS thread. The screen session is `krylov-experiments`; its log is
`artifacts/run/logs/marathon.log`. `XR_SCREEN_SESSION` and
`XR_MARATHON_OUTPUT` override the session name and working output directory.

Completed observations are retained on resume. An interrupted optimizer run
restarts from its specified initial point. Source, configuration and data
checks reject incompatible continuation. Stop signals the runner and its
active worker group and releases the writer lock.

For the main comparison alone:

```sh
bash scripts/run.sh run --workers 1 --libsvm --output artifacts/run/full
bash scripts/run.sh status --output artifacts/run/full
bash scripts/run.sh resume --output artifacts/run/full
```

After all four studies are complete, rendering and publication require no
optimizer calls:

```sh
"$XR_PYTHON" -B scripts/render_release.py --output artifacts/run
"$XR_PYTHON" -B scripts/release_audit.py --output artifacts/run
"$XR_PYTHON" -B scripts/paper_assets.py --run artifacts/run
```

## Methods and comparisons

XR/XR-F use chronological symmetric secant models, tested windows, virtual
steps, growing memory and safeguarded Armijo trials. The practical trial uses
the latest positive physical secant quotient. XR-F additionally uses endpoint
function values. Complete C controllers implement both solvers and the
MS-L-BFGS, SC-MSS, SC-SR1 and O-ACCEL-B comparators. L-CG_DESCENT uses author C
code; L-BFGS uses SciPy's compiled core with Python reverse communication.
All methods share the same counted objective/gradient interface.

The experiments cover controlled quadratics and nonlinear perturbations,
257 CUTEst instances, and 24 strongly convex full-batch logistic objectives
on eight LIBSVM datasets. Separate studies examine ablations, memory settings,
a full-matrix BFGS reference, tighter targets and full-memory local behavior.
The protocol, parameters and interpretation are documented below.

## Article assets

`artifacts/paper/figures` contains the five PDF figures used by the article;
`artifacts/paper/tables` contains its seven generated TeX tables. They are copied from the completed study outputs.

## Tests and documentation

```sh
PYTHONPATH=src "$XR_PYTHON" -B -m pytest -q -W error
ruff check src tests scripts
shellcheck scripts/*.sh env.sh
```

- [Algorithm correspondence](docs/AlgorithmCorrespondence.md): model formulas,
  numerical implementation and exact-real guarantees.
- [Practical trial](docs/PracticalVariant.md): positive-secant scaling and ablations.
- [Experimental protocol](docs/ExperimentProtocol.md): objectives, costs and profiles.
- [Preset rationale](docs/PresetRationale.md): parameter choices and sensitivity study.
- [Competitors](docs/CompetitorAudit.md): sources, implementations and numerical policies.
- [Paper assets](docs/PaperExperiments.md): generation and TeX inclusion.
- [Numerical interpretation](docs/NumericalFindings.md): conditioning and observed regimes.

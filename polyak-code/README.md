# Two Answers on Heavy-Ball Dynamics: computations and figures

This Python package provides the numerical experiments, figure programs and
exact mathematical witnesses for both parts of *Two Answers on Heavy-Ball
Dynamics*. It publishes the data archives `part1/proof/proof.tar.xz` and
`part2/proof/proof.tar.xz` for independent exact verification.

## Run

Use Python 3.13 and the pinned dependencies in
[requirements.txt](requirements.txt). Run from this directory:

```sh
python -m pip install -r requirements.txt
python verify_all.py --part1-only --jobs 4
python verify_all.py --part2-only
python verify_all.py --jobs 8
python verify_all.py --jobs 8 --figures
python figures/make_all.py
python figures/make_all.py --data
```

Each verification command constructs and packages the selected exact data
after its checks succeed. The full command runs the mathematical programs
and both archive pipelines. `--part1-only` uses the complete certificate
profile, with 4000 continuation slabs for each of P1, P2 and P5;
`--part2-only` constructs the five selected Part II examples.
`--figures` adds figure generation to the full verification command.
Logs and run manifests are written to `verification/`.

`figures/make_all.py` renders from cached data and generates missing inputs
with the commands it prints. `--data` recomputes all figure data and can take
several hours. PDFs go to `figures/pdf/`, PNG previews and numerical caches
to `data/`. `HB_FIGURES` overrides the PDF destination;
`HB_FONT_DIRECTORY` supplies an optional font directory. Plot spacing is
set in `figures/style.py` and `figures/hbstyle.py`; each figure program
controls its panel layout.

## Mathematical components

| Location | Content |
| --- | --- |
| `part1/hb_an/base`, `upper`, `struct` | Spiral identities, dual factorization, switching points, optimality systems and asymptotic identities |
| `part1/hb_an/analytic`, `regimes` | Rational P2 arc, critical P5 data, continuation, endpoint identification, signs and branch derivatives |
| `part1/hb_an/lower`, `part1/spiral` | Initialization from rest, uniform lower bounds and spiral kernel |
| [part1/certification](part1/certification/README.md) | Exact algebra, interval checks and rational witnesses for the Part I classification |
| `part1/rate.py` | Numerical evaluation of the four-family rate |
| `part2/general_identities.py`, `convexity.py`, `threshold_identities.py` | General tuning, phase, convexity, Farey, edge and junction identities |
| `part2/prop13_check.py`, `convgap_check.py`, `exact_313.py`, `plateaus/` | Numerical examples and periodic calculations |
| [part2/certification](part2/certification/README.md) | Exact witnesses for the two rational tunings, mixed plateaus 2/9 and 5/21, and the exact two-lag point 3/13 |
| `figures/`, `part2/hbgeom.py` | Figure programs, phase geometry and finite periodic linear programs |

Part I combines exact rational algebra, Bernstein and Taylor sign bounds,
and parametric Krawczyk contraction tests. Floating-point calculations
propose centers and inverse matrices; Arb checks inclusions and inequalities
with outward rounding. The certificate profiles contain 26 suites (`proof`)
and 27 suites (`complete`). Exact export requires a successful full selected
profile, 4000 slabs per continued family and matching source/dependency hashes.

Figures display the mathematical constructions and numerical approximations,
including frequency-grid searches and finite-period envelopes.

## Data archives

The contracts are specified in [part1/proof](part1/proof/README.md) and
[part2/proof](part2/proof/README.md). Both archives contain mathematical JSON
and manifests. Independent checkers establish the source identities,
interval bounds, root existence and optimality from these data.

# Part I mathematical certification

This component verifies the polynomial identities, sign bounds, critical
data and continuation systems for Part I of *Two Answers on Heavy-Ball
Dynamics*. It exports exact source expressions and finite witnesses through
[part1/proof/proof.tar.xz](../proof/README.md).

## Commands

Use Python 3.13 and the pinned [dependencies](../../requirements.txt).
Run from the [package root](../../README.md):

```sh
python -m pip install -r requirements.txt
python -m part1.certification verify --jobs 4
python -m part1.certification verify --profile complete --jobs 4
python -m part1.certification export
python -m part1.certification check-bundle part1/certification/generated/math
python -m part1.certification regen --jobs 4
python -m part1.certification package
python -m part1.certification check-bundle part1/proof/proof.tar.xz
```

`verify` runs the selected suites. The default `proof` profile has 26 suites,
including the exact rational P2 checks and 4000 continuation slabs for each
of P1 and P5. The `complete` profile adds the independent P2
field/continuation cross-check: 27 suites and 12000 slabs in total.
`--group` and `--slabs` select smaller verification runs; export requires
all suites of the chosen profile, 4000 slabs per continued family and
matching source/requirements hashes.

`regen` runs verification, failure controls, exact export, format validation
and archive packaging. It writes diagnostics to `generated/verification`,
mathematical JSON to `generated/math`, and the archive to
`part1/proof/proof.tar.xz`. `--out` selects a separate work directory and
places its archive there. Regeneration cleans output directories bearing
its generation marker. The package command
`python verify_all.py --part1-only --jobs 4` runs the complete pipeline.

`package` creates the deterministic archive from `generated/math` and writes
a byte-identical detached `part1/proof/manifest.json`. `check-bundle`
validates member names, formats, byte lengths and hashes.

## Mathematical components

| Location | Purpose |
| --- | --- |
| `algebra/` | Source systems, wave algebra, quotient-field arithmetic, Bernstein and Taylor methods |
| `checks/` | Callable exact/Arb suites, thresholds, regularity, asymptotics and continuation signs |
| `interval.py` | Parametric Krawczyk inclusions, contractions, derivative enclosures and adjacent-slab overlap |
| `branch_checks.py` | P1/P2/P5 signs, regularized central expressions and infinite-lag tails |
| `endpoints.py` | Exact endpoint identities and identification in the continued branches |
| `certificates/` | P2/P5/startup formulas, finite witnesses and the rational-data schema |
| [PROVENANCE.json](PROVENANCE.json) | Source provenance included in the exported manifest |

P1 uses `z=1/G` and unknowns `(A,B)`. P5 uses `h=G-1` and unknowns
`(A,B,y,P,D,w2,w3)`; its four primal equations are divided by `h` before
clearing denominators. Each check records a verdict and raises on failure.
NumPy/SciPy propose continuation centers and inverse matrices; Arb checks
inclusions and inequalities with outward rounding.

Generated verification reports are ignored by Git. Generators, source
provenance, the archive schema and the packaged proof archive are retained.

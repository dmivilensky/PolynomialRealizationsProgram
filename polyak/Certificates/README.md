# Mathematical data and formal certificates

The producer [polyak-code](../../polyak-code/README.md) supplies two data-only
archives. This directory contains the source descriptors and generated inputs;
all converters belong to the verification tools.

| Group | Descriptor | Workspace-local archive | Generated Lean inputs |
| --- | --- | --- | --- |
| Part I | [Source.json](Source.json) | `polyak-code/part1/proof/proof.tar.xz` | 244, including five under `polyak/Boundary` |
| Part II | [PartII/Source.json](PartII/Source.json) | `polyak-code/part2/proof/proof.tar.xz` | 14 |

Both descriptors select `transport: local`. Their `archive_path` is relative
to the workspace root; `archive_bytes` and `archive_sha256` pin the accepted
bytes. Every acquisition validates the local archive, including cached runs.

[Tools/Certificates/Registry.py](../../Tools/Certificates/Registry.py) registers
both local converters and the Part I Python requirements, separately from the
archive contract. `Source.json` is the source of the default archive path.
The [Part I converter](../../Tools/Certificates/Polyak/README.md) and Part II
converters read bounded JSON, verify member names and integrity, and generate
an allowlisted set of Lean files in isolation. The Lean build proves identities,
inequalities, continuation covers, source bridges and the theorems using these
inputs. Archive hashes establish the identity of the input data.

From the workspace root:

```sh
python3 -m Tools.Verification.Check polyak --offline --require-complete --jobs 2
```

Online mode can install missing pinned Python dependencies; archive
transport stays local. `--archive PATH` explicitly overrides only the
primary Part I archive and retains the same byte checks. Independent proof
replay is available with `--replay` or selected `--replay-scope` flags.

`python3 -m Tools.Maintenance.Clean` removes reproducible Lean inputs and caches.
Source descriptors, the tools registry, handwritten proofs and both producer
archives under `polyak-code` are preserved. The next check restores the inputs
from those archives. [PartII/README.md](PartII/README.md) describes the second group.

## Part I interchange contract

The archive identifies its format as `HEAVY_BALL_PART1_PROOF`, its `version`
as `1`, and its schema as `heavy-ball-part1-proof-v1`. Its regular JSON members
are `manifest.json`,
`schema.json`, `mathematics.json`, `interval-p1.json`, `interval-central.json`,
`checks.json` and the optional complete-profile `interval-p2.json`.
The manifest gives byte counts and SHA-256 values for the other members.
Check reports record the producer verification profile and source identity.

A polynomial is a record such as
`{"variables":["x","y"],"terms":[["3/5",[1,2]]]}`, denoting `(3/5)xy²`.
Terms have nonzero coefficients and strictly ordered exponent tuples.
Rationals are reduced strings with positive denominators. Rational functions
use numerator and denominator polynomials in the same variable order. Lean separately proves nonvanishing where needed.

Continuation records contain rational endpoints, centers, positive radii,
inverse matrices, variable order and source-system identifiers. Lean checks
the parameter cover, derivatives, contraction and signs. The 44 initialization
records contain rational expressions and finite physical-branch witness trees
for integer-Horner
checking at scale `2^64`; maintained proofs relate these data to the actual
source expressions. Both archives use the data-only contracts documented by
the producer.

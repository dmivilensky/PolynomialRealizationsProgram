# Polyak mathematical archive consumer

This directory belongs to the Lean project. The independent
[polyak-code](https://github.com/dmivilensky/PolynomialRealizationsProgram/tree/main/polyak-code) package supplies only
`part1/proof/proof.tar.xz`; it has no imports, paths or generators for this
project. The supplier's original figure pipeline is preserved.

The archive location, exact byte count and SHA-256 are pinned in
[`polyak/Certificates/Source.json`](../../../polyak/Certificates/Source.json).
The descriptor uses `transport: local` and the workspace-relative path
`polyak-code/part1/proof/proof.tar.xz`. Acquisition checks that actual file on
every invocation. There is no archive download or fallback to an old cache.
[Registry.py](../Registry.py) registers the converter and pinned Python dependencies;
the archive path belongs only to `Source.json`.

The normal entry point, from the workspace root, is:

```sh
python3 -m Tools.Verification.Check polyak --offline --require-complete --jobs 2
```

The shared hook verifies the archive, prepares the pinned generator environment,
invokes [`PolyakPrepare`](../PolyakPrepare.py), checks the declared coverage and
builds the Lean package with its source/axiom audit. Without `--offline`, missing
Python dependencies may be installed; proof archive acquisition remains local.
`--list` does not prepare data or install anything.

`PolyakPrepare` reads only bounded regular JSON members. It rejects duplicate
keys and members, noncanonical rational data, incompatible versions, unsafe
member paths, size/hash mismatches and executable payloads. It does not unpack
or run supplier programs. Its cache is under `.lake/certificates/polyak`.

The local generators use the four mathematical groups as follows:

| Group | Local conversion | Output |
| --- | --- | --- |
| P₂ | Exact source polynomials and rational identities, moments and finite signs | 17 files |
| P₅ | Exact divided-system and critical/Jacobian coefficient arrays | 5 files |
| Initialized spiral | Archived rational expressions and physical-branch witness trees, independently related to the actual source formulas | 63 files |
| Continuation | P₁/P₅ systems, full root covers, endpoint transfers, geometry, lags and derivative enclosures | 159 files |

All declared outputs are generated into a temporary directory before installation.
An explicit allowlist prevents overwriting maintained analytic proof modules.
Files whose bytes match are retained. A generation receipt can be reused only
when the archive, generator sources, dependencies and every output still match.
The shared manifest declares 244 generated files in total. Preparing their
exact data is followed by the maintained proofs of global continuation,
all lags, endpoint identities and optimality.

With the consumer dependencies already installed, direct preparation and
comparison are available without building:

```sh
python -m Tools.Certificates.PolyakPrepare --offline --archive polyak-code/part1/proof/proof.tar.xz
python -m Tools.Certificates.PolyakPrepare --offline --archive polyak-code/part1/proof/proof.tar.xz --check
```

`--archive PATH` explicitly supplies local archive bytes, which must still
match `Source.json`. `--root PATH` generates into an isolated destination.
The default source is the pinned archive in the local producer tree;
`--root` changes only the generated-output destination.

The ordinary Lean kernel checks coefficient identities and finite witnesses;
the maintained analytic modules prove feasibility, infinite tails and
optimality. SHA-256, member manifests and external `passed` reports serve
provenance, never as axioms. Independent proof replay remains
`python3 -m Tools.Verification.Replay polyak` after a completed build.

The preparation pipeline has regenerated all 244 inputs byte for byte from the
fresh local archive. Producer verification and mathematical article coverage
are recorded in the package's article correspondence. Appendix C uses the
constructive real filter-SOS factorization of all actual source polynomials;
the standalone arbitrary-degree single-filter Fejér–Riesz theorem is not claimed.

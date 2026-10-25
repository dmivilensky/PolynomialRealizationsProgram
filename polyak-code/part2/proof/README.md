# Part II mathematical data contract

The [producer](../certification/README.md) writes
`part2/proof/proof.tar.xz` automatically through
`python verify_all.py --part2-only` or the full verification command.
It is a deterministic XZ-compressed USTAR archive of six regular UTF-8 JSON files.

| Member | Mathematical content |
| --- | --- |
| `rational.json` | Two exact rational tunings, source polynomial coefficients, phase-floor partition and Bernstein depth |
| `exact313.json` | Scalar compatibility root, Hermite coefficients, domain and sign reserves, location bounds |
| `plateaus.json` | Two boundary determinant brackets, support fractions, source matrices, kernel/weight/pinning enclosures, lifted signed lags and global polynomial covers |
| `trigonometry.json` | Rational enclosures of sine and cosine at finitely many rational angles |
| `system313.json` | Three-dimensional contact-system box, approximate inverse Jacobian and exact arithmetic evaluation parameters |
| `manifest.json` | Format, version, schema, byte length and SHA-256 digest of each mathematical member |

The manifest has exactly the keys `format`, `version`, `schema`, `members`.
They identify `HEAVY_BALL_PARTII_PROOF_DATA`, version `1`, and
`heavy-ball-part2-proof-v1`. Each other member has exactly `schema`, `kind`
and `data`; `kind` is its filename without `.json`. Each data group carries
its own mathematical schema version.

Every rational number is a reduced `[numerator, denominator]` pair with a
strictly positive denominator. Dimensions, indices and depths are JSON
integers; an interval is a pair of rational endpoints. Exact checking
compares coefficients and expressions with source formulas, proves signs
by exact arithmetic and establishes existence of the proposed roots.
Checksums establish byte identity.

Names are flat, fixed and unique. JSON object keys are unique, and all
numeric values are rational pairs or integers. Consumers can impose size
and depth bounds. Archive metadata is normalized and members are sorted,
so unchanged mathematical input yields identical archive bytes.

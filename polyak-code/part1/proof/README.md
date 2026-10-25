# Part I mathematical data contract

The [producer](../certification/README.md) publishes exact Part I data as
`part1/proof/proof.tar.xz`, a flat XZ-compressed tar archive of JSON files.

| Member | Content |
| --- | --- |
| `manifest.json` | Format, version, byte lengths, SHA-256 digests and evidence provenance |
| `schema.json` | JSON Schema for the interchange records |
| `mathematics.json` | Groups `core`, `p2`, `p5`, `startup`: exact source expressions and finite witnesses |
| `interval-p1.json` | Rational proposals for the P1 continuation |
| `interval-central.json` | Rational proposals for the regularized P5 continuation |
| `checks.json` | Structured mathematical check reports |
| `interval-p2.json` | Independent P2 continuation, present in the complete profile |

The manifest has `format: "HEAVY_BALL_PART1_PROOF"`, `version: 1` and
`schema: "heavy-ball-part1-proof-v1"`. Its `members` object maps every member
except `manifest.json` to `{"bytes": integer, "sha256": hexadecimal_string}`.
The detached `manifest.json` and `schema.json` in this directory are identical
to their archived counterparts. Member names are flat and relative;
metadata uses fixed timestamps. Members are regular files with unique names.

Each mathematical record declares the same schema identifier. Rational
numbers are reduced strings with positive denominator, such as `"-2"` or
`"3/5"`. A polynomial has the form

```json
{"variables":["x","y"],"terms":[["-2",[0,0]],["3/5",[1,2]]]}
```

This represents −2 + (3/5)xy². Variable order is significant; terms are
nonzero and strictly ordered by their exponent tuples. A rational expression
has `numerator` and `denominator` polynomial records and is evaluated where
its denominator is nonzero.

The `core` group includes the spiral master polynomial, switch polynomials,
Chebyshev polynomials and source equations for P1, P2 and P5. The P2 group
supplies rational-coordinate formulas and finite sign data. The P5 group
includes regularized equations, critical quintic data, Jacobian blocks,
a dual quotient and divided-slack coefficients. The startup group supplies
44 exact source inequalities and finite physical-branch interval witnesses.

A startup witness uses `integer-horner-physical-branch-v1`: at scale 2⁶⁴,
integer interval Horner evaluation rounds products outward. Each dyadic
subinterval in the growth factor has a rational interval for the positive
root of the master polynomial. The polynomial has the required signs at
the two root-interval boundaries throughout the growth-factor subinterval.

Continuation proposals declare their parameter, unknown order, source
equations, parameter domain and exact adjacent cover. Each box contains
a rational parameter interval, center, positive radii and inverse matrix.
Exact verification recomputes Krawczyk images, contraction bounds,
derivative enclosures, adjacent-box overlap and sign bounds from these
data and the source equations.

JSON Schema specifies the structural contract. Exact checking also verifies
rational reduction, term order, exponent dimensions, interval order and the
mathematical conditions represented by the records. `passed` fields record
producer check results; hashes establish byte identity.

The manifest records `provenance.verification_scope` (`current-producer` or
`historical-import`), `fresh_verification`, and source/dependency digests.
These fields identify the evidence associated with the data.

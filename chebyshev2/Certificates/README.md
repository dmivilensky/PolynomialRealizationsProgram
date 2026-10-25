# chebyshev2: the 1.000013 certificate

`Compact.ReferenceBase.uniform_gain_improvement` is the endpoint. Lean checks
the actual reference trajectory on all 2,519 cells, both complete quadratures,
the exterior logarithmic tail and the one-determinant base. The sufficient sine
bound comes from chebyshev1. No saved success report is a proof premise.

[Source.json](Source.json) identifies the GitHub archive and its expected hashes.
Only the reference parameters in `claims.json` and the supporting trajectory
are decoded; bundled upstream programs are never executed.

`python3 -m Tools.Verification.Check chebyshev2` automatically downloads the
pinned archive when needed, reconstructs the proposals, and compares all
reference, residual and quadrature witnesses before the Lean build. The same
preparation runs as part of `Check all`; validated unchanged inputs are cached.

```sh
python3 -m Tools.Certificates.ReferenceInputs --offline --check
python3 -m Tools.Certificates.VerifyResidualBatches --offline --check
python3 -m Tools.Certificates.VerifyContact --offline --check
python3 -m Tools.Certificates.VerifyAmplitude --offline --check
python3 -m Tools.Verification.Check chebyshev2
```

Omit `--offline` for the first archive fetch. The `--check` commands regenerate
and compare source witnesses without changing proof files; the final command
checks the full mathematical chain. To regenerate proposals after fetching the archive, run
`python3 -m Tools.Certificates.ContactProposals --offline` and
`python3 -m Tools.Certificates.AmplitudeProposals`, then their corresponding verifiers.
Caches live under `.lake/certificates/chebyshev2`.
An optional independent kernel replay is
`lake env lean --run Tools/Verification/Replay.lean 'chebyshev2.Certificates.Compact.ReferenceBase'`.

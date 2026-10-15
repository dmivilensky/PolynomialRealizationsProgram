# 2610.05164v2: the 1.000013 certificate

`Compact.ReferenceBase.uniform_gain_improvement` is the endpoint. Lean checks
the actual reference trajectory on all 2,519 cells, both complete quadratures,
the exterior logarithmic tail and the one-determinant base. The sufficient sine
bound comes from 2606.16671v2. No saved success report is a proof premise.

[Source.json](Source.json) identifies the GitHub archive and its expected hashes.
Only the reference parameters in `claims.json` and the supporting trajectory
are decoded; bundled upstream programs are never executed.

```sh
python3 Scripts/ReferenceInputs.py --offline --check
python3 Scripts/VerifyResidualBatches.py --offline --check
python3 Scripts/VerifyContact.py --offline --check
python3 Scripts/VerifyAmplitude.py --offline --check
python3 Scripts/Check.py 2610.05164v2
```

Omit `--offline` for the first archive fetch. The `--check` commands regenerate
and compare source witnesses without changing proof files; the final command
checks the full mathematical chain. To regenerate proposals, use
`ContactProposals.py` and `AmplitudeProposals.py`, then their corresponding verifiers.
Caches live under `.lake/certificates/2610.05164v2`.
An optional independent kernel replay is
`lake env lean --run Scripts/Replay.lean '«2610.05164v2».Certificates.Compact.ReferenceBase'`.

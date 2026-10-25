# Part II certificate inputs

[Source.json](Source.json) pins the local archive
`polyak-code/part2/proof/proof.tar.xz` by size and SHA-256.
The [converter registry](../../../Tools/Certificates/Registry.py) selects
`Tools.Certificates.PolyakPartIIPrepare` for this source.

Generate the archive in the computational package:

```sh
cd polyak-code
python verify_all.py --part2-only
```

Run verification from the workspace root:

```sh
python3 -B -u -m Tools.Verification.Check polyak --offline --require-complete --jobs 2
```

The converter validates the archive and its bounded JSON members, generates
14 allowlisted Lean inputs in isolation, and installs changed files. Both
archive groups are prepared by the central command; unchanged inputs and
proofs are cached.

The data contain exact coefficients, intervals, root boxes, preconditioners
and polynomial covers for five examples: the two rational tunings, mixed
plateaus with anchors 2/9 and 5/21, and the exact two-lag point 3/13.
Maintained proofs in `polyak/CertifiedExamples` define the source formulas
and prove the identities, signs, root existence and final conclusions.

For an independent kernel replay of these examples and their generated data,
add `--replay-scope CertifiedExamples --replay-scope Certificates/PartII`.
The shared `Clean` removes generated inputs using the exact allowlist in
`Tools/Certificates/PolyakPartIIOutputs.py`; source descriptors and maintained
proofs are preserved.

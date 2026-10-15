# PolynomialRealizationsProgram

Lean proofs for [2606.16671v2](2606.16671v2/README.md) and
[2610.05164v2](2610.05164v2/README.md). Definitions and intermediate lemmas live
under the corresponding article name; the second article reuses the first.

```sh
lake exe cache get
python3 Scripts/Check.py 2606.16671v2
python3 Scripts/Check.py 2610.05164v2
```

Each command checks its entire [Check](2606.16671v2/Check.lean) /
[Check](2610.05164v2/Check.lean) file, including the ordered article showcase,
source coverage and transitive axioms. The builder limits concurrent Lean processes.
`python3 Scripts/Check.py all` checks both through
[PolynomialRealizationsProgram.lean](PolynomialRealizationsProgram.lean), also the default `lake build` target.

Each article has a correspondence table and a short architecture guide.
[Trust.md](Trust.md) explains the actual axioms and the witness-generator boundary.
`python3 Scripts/CheckDocumentation.py` checks object, field and generator annotations;
add `--parse` to validate them with Lean's parser using existing compiled modules.

`python3 Scripts/Clean.py --dry-run` lists disposable files;
`python3 Scripts/Clean.py` removes caches, downloads, logs and temporary artifacts.
It preserves the generated Lean witnesses required by the proofs. The resulting
package contains only proof sources, generators, documentation, papers and build configuration.

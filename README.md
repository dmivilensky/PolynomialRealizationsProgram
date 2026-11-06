# PolynomialRealizationsProgram

Lean proofs for [bezout](bezout/README.md), [chebyshev1](chebyshev1/README.md),
[chebyshev2](chebyshev2/README.md), [jacobi](jacobi/README.md),
[krylov](krylov/README.md), [polyak](polyak/README.md), and
[nesterov](nesterov/README.md).

Mathematical sources stay in their article packages. Shared tooling lives in:

```text
Tools/
  Verification/   Audit.lean, All.lean, source/showcase checks and kernel replay
  Certificates/   Reference inputs, numerical proposals and certificate verifiers
  Maintenance/    Distribution cleanup
  Tests/          Tooling regression tests
```

Run Python tools as modules from the project root, for example
`python3 -m Tools.Verification.Check all`.
The `Verification` Lake library uses `Tools` as its source directory: its modules
are `Verification.Audit` and `Verification.All`, without an extra root Lean file.
`Check all` refreshes `All.lean` from the discovered package checks before building;
Lean package discovery requires no Python registry. Packages with generated
certificate inputs register their local converters separately in
[Tools/Certificates/Registry.py](Tools/Certificates/Registry.py).

```sh
lake exe cache get
python3 -m Tools.Verification.Check chebyshev1
python3 -m Tools.Verification.Check chebyshev2
python3 -m Tools.Verification.Check jacobi
python3 -m Tools.Verification.Check krylov --require-complete
python3 -m Tools.Verification.Check polyak
python3 -m Tools.Verification.Check bezout --offline --require-complete --replay
python3 -m Tools.Verification.Check nesterov --offline --require-complete --replay
```

Each command checks the selected directory's `Check.lean`, source coverage and
transitive axioms. The builder uses two concurrent Lean processes by default;
`--jobs N` sets a larger limit when CPU and memory permit.
Newly ready dependencies can start while an independent certificate is still
running; the process limit also bounds the submitted build queue.
`python3 -m Tools.Verification.Check all` discovers the registered package roots
with a `Check.lean` entry. Internal checker modules belong to their parent package. `--list` shows the selected modules without building.
`lake build` uses the [shared aggregate](Tools/Verification/All.lean) maintained by
that command.

All common tools accept a source directory, or `all` (the default):

```sh
python3 -m Tools.Verification.Check DIRECTORY
python3 -m Tools.Verification.CheckCorrespondence DIRECTORY
python3 -m Tools.Verification.Replay DIRECTORY
```

New packages need their normal Lake library registration and a `Check.lean`
entry point. Source directories and module roots, including escaped dotted names,
come from `lakefile.toml`. A sibling public root file is optional. No source-discovery script
needs the new package's name. Replay uses existing compiled artifacts and never
builds them.

`python3 -m Tools.Maintenance.Clean --dry-run` lists disposable files;
`python3 -m Tools.Maintenance.Clean` removes caches, downloads, logs and temporary artifacts.
It also removes all declared Polyak inputs regenerated from the local `polyak-code`
archives: 244 Part I inputs, including five under `polyak/Boundary`, and 14 Part II inputs. Source descriptors, converter registrations,
handwritten proofs and other packages’ checked-in witnesses are preserved. The next
Polyak verification reads both local archives and prepares these inputs automatically.

Run the tooling tests after `python3 -m Tools.Verification.Check all` with
`python3 -m unittest discover -s Tools/Tests -p 'Test*.py' -v`.
The kernel rejection tests use the compiled residual checker from chebyshev2
and the exact certificate checkers from polyak.
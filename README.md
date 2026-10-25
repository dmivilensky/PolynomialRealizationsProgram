# PolynomialRealizationsProgram

Lean proofs for [chebyshev1](chebyshev1/README.md),
[chebyshev2](chebyshev2/README.md), and [polyak](polyak/README.md).
Definitions and intermediate lemmas live under the corresponding article name.
The second Chebyshev package reuses the first; Polyak also uses their exact
arithmetic and interval checkers.
The [polyak package](polyak/README.md) formalizes
[Two Answers on Heavy-Ball Dynamics](polyak.pdf), with its own build and complete
source/axiom audit. Its [ordered showcase](polyak/Article.lean) and
[correspondence](polyak/ArticleMap.md) cover both parts, all 144 numbered
results and the five selected numerical examples. The computational package
[polyak-code](polyak-code/README.md) supplies two pinned mathematical JSON archives
through [Part I Source.json](polyak/Certificates/Source.json) and
[Part II Source.json](polyak/Certificates/PartII/Source.json).
Polyak reads both archives locally from `polyak-code`; they stay in that
package. Chebyshev II retains
its pinned external certificate source.

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
python3 -m Tools.Verification.Check polyak
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

To replay a new namespace subtree against previously checked compiled dependencies,
use `python3 -m Tools.Verification.Replay polyak --scope Farey`, or combine it
with the normal cached build and complete audit using
`python3 -m Tools.Verification.Check polyak --jobs 1 --require-complete --replay-scope Farey`.
The subtree is selected by its package-relative directory. Repeat `--scope` or
`--replay-scope` to replay a union of subtrees with cross-dependencies, as in
the [polyak command](polyak/README.md). The stock kernel helper rejects a
baseline that already contains declarations owned by any selected subtree. This avoids repeating
unchanged Part I certificate checks during Part II work; `--replay` explicitly
requests the full package instead.

The [showcases](polyak/Article.lean) and [correspondence tables](polyak/ArticleMap.md)
record manual comparison with the article PDFs. Automation checks their local Lean
links and agreement with each other. A map with a pinned `article-source` also
checks every result's order, number, label, kind and title, the unnumbered
inventory, and whether changes to the article invalidate its review. Semantic
equivalence still requires mathematical comparison of the statements and Lean
types; compilation alone does not establish it. The maps are optional for a
plain Lean package. [Trust.md](Trust.md) explains the actual axiom checks.

Package-specific witness generation remains under `Tools/Certificates`.
Chebyshev II automatically fetches its pinned GitHub archive and reconstructs
and compares its reference, residual and quadrature witnesses before building.
The heavy-ball archive reader and generators are
[PolyakPrepare](Tools/Certificates/PolyakPrepare.py) and
[Polyak](Tools/Certificates/Polyak/README.md); generated Lean literals remain
under `polyak/Certificates` and `polyak/Boundary`.

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

Python 3.11 or newer is required by the shared tools (`tomllib`). The Lean
version is pinned in [lean-toolchain](lean-toolchain); Mathlib and LeanCert are
pinned in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json).
Polyak certificate conversion uses the pinned dependencies in
[Tools/Certificates/Polyak/requirements.txt](Tools/Certificates/Polyak/requirements.txt).
Reproducing experiments and figures uses Python 3.13 and the larger dependency
set documented in [polyak-code](polyak-code/README.md).

# polyak

Lean formalization of [Two Answers on Heavy-Ball Dynamics](../polyak.pdf). The two parts contain the main results; Appendices A–I
supply their proofs. [polyak.lean](../polyak.lean) is the public import,
[Article.lean](Article.lean) presents the statements in article order, and
[Check.lean](Check.lean) audits the complete library.

## Verification

From the workspace root:

```sh
python3 -B -u -m Tools.Verification.Check polyak --offline --require-complete --jobs 2
```

The command checks both local proof archives, prepares the generator environment,
restores 244 Part I inputs and 14 Part II inputs, checks article correspondence,
and builds the Lean proofs with a transitive axiom audit. Unchanged inputs and
compiled proofs are cached. `--offline` requires the pinned Python dependencies
to be installed; without it, the tool can install missing dependencies.
Proof archives are always read from the local `polyak-code` directory.

- [Part I source](Certificates/Source.json): `polyak-code/part1/proof/proof.tar.xz`.
- [Part II source](Certificates/PartII/Source.json): `polyak-code/part2/proof/proof.tar.xz`.
- [Data contracts and conversion](Certificates/README.md).
- [Part I generators](../Tools/Certificates/Polyak/README.md).
- [Converter registry](../Tools/Certificates/Registry.py).

Each source descriptor pins the archive's size and SHA-256. The converters read
mathematical JSON and generate Lean inputs. Lean proves the source identities,
interval bounds, feasibility and optimality using those inputs.

The computational package produces the archives with:

```sh
cd polyak-code
python verify_all.py --part1-only --jobs 4
python verify_all.py --part2-only
```

Each command verifies, exports and packages its part automatically. When an
archive changes, review its contents and update the corresponding descriptor's
size and SHA-256. Independent kernel replay is available through `--replay`;
`--replay-scope DIRECTORY` selects a package-relative subtree and can be repeated
for a union of subtrees.

## Article correspondence

[ArticleMap.md](ArticleMap.md) and [Article.lean](Article.lean) cover all 144
numbered results in PDF order, with printed numbers, titles and TeX labels.
The map also covers 36 groups of unnumbered mathematics.
[Architecture.md](Architecture.md) describes the proof dependencies.

The correspondence records the hypotheses, normalizations and quantifiers of
the actual Lean declarations. In Part I, one five-dimensional function and one
start work for every horizon. For an arbitrary measure in Part II, one positive
lower-bound constant works for all horizons, with a finite-dimensional
realization for each horizon.

The map pins the article's SHA-256. Verification checks the ordered inventory,
statement titles and labels, local proof links, and each showcase block's
references. Article edits require a mathematical review and an updated source
pin. The Lean audit includes private and generated declarations and permits
only `propext`, `Classical.choice` and `Quot.sound` as transitive axioms.

## Cleanup

```sh
python3 -m Tools.Maintenance.Clean --dry-run
```

`Clean` removes caches and all 258 declared generated inputs. It preserves
handwritten proofs, tools, source descriptors and both proof archives.
The next verification command restores the inputs before building Lean.

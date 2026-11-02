# jacobi

Article: [jacobi](../jacobi.pdf). The Lean package is `jacobi`.
It reuses `chebyshev1` and `chebyshev2` for realizations, Jacobi matrices,
Green packing, Hilbert-space operators and the sine normalization.

```sh
python3 -m Tools.Verification.Check jacobi
```

[Check.lean](Check.lean) checks the entire mathematical library and its axiom
dependencies. [Article.lean](Article.lean) lists article statements and labeled
proof ingredients in source order. [ArticleMap.md](ArticleMap.md) gives their
exact coverage; [Architecture.md](Architecture.md) explains the proof layers.
Import `jacobi` to use the mathematics.

The main theorem and proposition conclusions are checked, including the
compact-test and full-domain differential realization, exact exponential
Green kernel and complete packed-density spectrum with multiplicities.
Section 5 includes all nonnegative-link three-term realizations, attained
closed-fibre minima, the standard one-sided limit, the resolvent-flow descent
and the sharp symmetric endpoint comparison. The sampled flow plot in
Figure 2 and decimal illustrations in Appendix E.2 are excluded from
numerical certification; their analytic inputs are proved.

With existing dependencies, `lake env lean jacobi/Check.lean` checks the entry
point without rebuilding them. Independent kernel replay uses
`python3 -m Tools.Verification.Replay jacobi`.
See [Trust.md](../Trust.md) for the precise trust boundary.


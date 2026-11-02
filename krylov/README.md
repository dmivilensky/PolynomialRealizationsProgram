# krylov

Lean proofs for [Adaptive Krylov Methods under Hessian Variation](../krylov.pdf):
secant information, sharp perturbation and minimax bounds, spectral design,
extremal Krein strings, function-compatible obstructions and local convergence.
The construction reuses the earlier [chebyshev1](../chebyshev1/README.md) and
[chebyshev2](../chebyshev2/README.md) packages.

```sh
python3 -m Tools.Verification.Check krylov --require-complete --offline --jobs 2
```

[Article.lean](Article.lean) checks the article statements in printed order.
[ArticleMap.md](ArticleMap.md) records their exact declarations, hypotheses,
normalizations and additional unnumbered mathematics.
[Architecture.md](Architecture.md) describes the proof layers.
[Check.lean](Check.lean) checks complete source coverage and the transitive
axioms of every owned declaration. Use `import krylov` for the library.

The algorithm results concern exact mathematical executions. Rational
barriers certify the five-significant-digit constants printed in the article.
The companion-paper string remarks have their own correspondence notes in
the map. Numerical experiments and floating-point implementations are supplied
by [krylov-code](../krylov-code/README.md).

[Trust.md](../Trust.md) explains the distinction between imported runtime
axioms and dependencies of mathematical proofs.


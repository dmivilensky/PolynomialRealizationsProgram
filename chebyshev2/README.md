# chebyshev2

[Article](../chebyshev2.pdf): the continuum, spectral and variational theory
of Chebyshev realization gains. The analytic statements are formalized,
including general measurable ground states/speeds, actual ODE filters,
dual-certificate transfer, primal-family derivatives and exact feasibility,
and the local obstruction theorem. Results of [chebyshev1](../chebyshev1/README.md)
are reused.

```sh
python3 -m Tools.Verification.Check chebyshev2
```

[Check.lean](Check.lean) is the complete verification file (Lake target `+chebyshev2.Check`).
[Article.lean](Article.lean) checks statements in article order;
[ArticleMap.md](ArticleMap.md) states the precise correspondences and exclusions;
[Architecture.md](Architecture.md) explains the proof layers.
Use `import chebyshev2` to import the mathematical library.

`Certificates.Compact.ReferenceBase.uniform_gain_improvement` proves the
unconditional uniform factor **1.000013**, including reducible matrices.
Its proof checks all 2,519 reference ODE cells, contact/amplitude integrals,
the exterior tail and the reference base, and uses the sine-energy bound from
chebyshev1. [Certificates](Certificates/README.md) explains reproduction.

Excluded numerical conclusions: the full-dual Table 2 values and factor
`1.000004`, the extra sine decimal precision, and the concrete primal certificate
of Proposition 11/Corollary 3. Their analytic implication theorems remain proved.
Experiments and Hypothesis 1 are excluded; the latter is a conjecture.
[Trust.md](../Trust.md) distinguishes imported runtime axioms from proof dependencies.

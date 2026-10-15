# 2606.16671v2

[Article](../2606.16671v2.pdf): *Chebyshev-Exact Acceleration under Hessian Variation, I: Sine-Jacobi Method*.
Sections 1–5 and Appendices A–E are formalized: realization algebra, sharp gains,
prefix optimality, Jacobi drift of every order, sine-chain endpoint/ODE analysis,
energy asymptotics and nonlinear Hessian bounds. Section 6 and Appendix F contain
experiments and are excluded.

```sh
python3 Scripts/Check.py 2606.16671v2
```

[Check.lean](Check.lean) is the complete verification file (Lake target `+«2606.16671v2».Check`).
[Article.lean](Article.lean) checks statements in article order;
[ArticleMap.md](ArticleMap.md) gives their declarations, and
[Architecture.md](Architecture.md) explains the proof layers.
Use `import «2606.16671v2»` to import the mathematical library.

`sineEnergy_decimal` proves `1.14269215 < c_sin < 1.14269221` for the actual
elliptic-profile integral; `sineEnergy_rounding` proves rounding to `1.1426922`.
Landen descent, singular endpoint control and quadrature error are proved here.
The generator only proposes integer intervals; kernel reduction checks them.
Remark 5.5's finite examples have rational certificates: amplification lies in
`(2.24, 2.25)`, `(12.8, 12.9)` and `(704, 705)` for its three drift fractions.
The printed numbers `2.3`, `13` and `700` are illustrative approximations.

Empty Jacobi blocks equal `1`. Operator norms are Euclidean and Hilbert–Schmidt
norms are Frobenius norms. The small-accuracy amplification approximation with
prefactor `1/2` assumes a positive drift fraction; at zero drift amplification is `1`.
The complete trust boundary is in [Trust.md](../Trust.md).

# 2610.05164v2: architecture

| Modules | Purpose and article chain |
| --- | --- |
| `Finite`, `Green`, `Packing` | All recurrence classes, sharp gains, centering and density packing → Theorems 2.1–2.3, A.1 |
| `Sobolev`, `Continuum` | Actual Hilbert spaces, positive compact/trace-class operators, l1 spectrum and Fredholm/cosh transfer → Theorem 2.4, Lemma 4 |
| `SineJacobi`, `SineContinuum` | Reused finite chain; Legendre/Mercer and theta realizations, exact energy series → Theorem 2.5, Proposition 2, Lemmas 5–7, Proposition 10's analytic formulas |
| `GroundState`, `PrescribedSpeed`, `Filters`, `HalfLine` | L1 ground state, measurable density construction, actual filters and common spectral measure → Theorems 3.1, 3.3, 5.1; Proposition 3 |
| `StateRegion` | Exact state range, parametrization and boundary rigidity → Propositions 7, 12; Lemma 8 |
| `Calibration`, `Comparison`, `Residual` | Contact minimizers, signed observations, integrated residual and cubic conjugate → Theorems 3.2, 3.4–3.5; Propositions 4–6, 8 |
| `DualCertificate`, `Calculus`, `Numerics` | General admissibility/transfer, endpoint normalization and sound error rules → Theorem 3.6, E.1; Lemmas 16–24 |
| `Primal` | Actual finite-dimensional moment/spectral C1 derivatives and contraction feasibility → Theorem 5.2, Lemma 25, Proposition 13 |
| `LocalObstruction` | Actual observation derivatives, tails and smooth mass-preserving perturbations → Theorem 6.1, Lemma 26 |
| `Certificates` | Source-bound trajectory, complete quadratures, tail and unconditional `1.000013` → Proposition 6 and Section 4.1 |
| `Article`, `Check` | Ordered statements and exclusions; complete import and axiom checks |

Finite comparisons and uniform filter continuity supply the primal spectral
derivatives. Exact contraction proves feasibility for the actual observation map;
it is a general theorem, separate from the excluded concrete numerical instance.
The certificate generators propose data; Lean proves their connection to the
actual ODE and integrals. Each source header identifies its role and downstream use.

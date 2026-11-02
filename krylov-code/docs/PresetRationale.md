# Solver presets and memory sensitivity

`src/xrbench/resources/methods.json` specifies the executable settings.
Every scheduled job records its effective arguments. The primary settings
are shared across problems.

| Method | Parameters | Rationale |
|---|---|---|
| L-BFGS | `m=20, maxls=20` | Our choice within the authors' recommended memory range 3–20; SciPy defaults to 10 pairs. |
| L-CG_DESCENT | `memory=11` | Author default and best tested memory in the paper's Section 8. |
| MS-L-BFGS | `m=8, M=8` | Published uniform L8M8 configuration. |
| SC-MSS | `m=3, q=5`, dense complement | Recommended SC-INF-D configuration. |
| SC-SR1 | `m=5, q=7`, Init. 2 | Preferred SC-INF experimental configuration. |
| O-ACCEL-B | `wmax=20, delta=1e-4, eps0=1e-12` | Published CUTEst experimental configuration. |
| XR / XR-F | `m0=min(10,n)`, cap `min(100,n)` | Our practical memory policy. |

The parameters count different information: L-BFGS pairs, CG directions,
simultaneous secants, and SC initialization observations have distinct costs.
SC initialization uses the current curvature and `q` preceding observations.
The fixed integers do not imply equal storage or equal work.

## Sources

- L-BFGS-B's [algorithm description, Section 2](https://people.sc.fsu.edu/~inavon/5420a/lbfgsb.pdf)
  recommends 3–20; [SciPy's API](https://docs.scipy.org/doc/scipy/reference/generated/scipy.optimize.fmin_l_bfgs_b.html)
  exposes memory 10 and `maxls=20`.
- [Hager–Zhang, Section 8](https://www.math.lsu.edu/~hozhang/papers/lcg.pdf),
  [DOI](https://doi.org/10.1137/120898097), motivates CG memory 11. Its small-
  dimension L-BFGS branch remains part of the author implementation.
- [Gubarev, Section 5](https://optimization-online.org/wp-content/uploads/2026/03/ms-lbfgs.pdf)
  fixes eight stored pairs and compares genuine multisecant counts. Its
  profiles do not establish a universal optimal count.
- [Brust–Erway–Marcia, Section 5](https://arxiv.org/abs/2209.12057)
  supplies the MSS defaults and dense initialization.
- [SC-SR1, Figures 2–3 and Appendix A.2](https://arxiv.org/abs/1607.03533)
  supplies the SR1 configuration.
- [Riseth, Sections 3.2 and 3.5](https://doi.org/10.1002/nla.2216)
  supplies O-ACCEL-B's memory, preconditioner and experimental regularization.

Source-specific searches and numerical decisions are documented in
[CompetitorAudit.md](CompetitorAudit.md).

## Sensitivity study

| Method | Values varied |
|---|---|
| L-BFGS | `m in {5,10,20}` |
| L-CG_DESCENT | `memory in {5,11,20}` |
| MS-L-BFGS | Eight stored pairs; `M in {2,4,8}` |
| XR / XR-F | `m0 in {5,10,20}`; cap 100 |

All other settings remain fixed. The cohort consists of four hash-selected
instances from each nonlinear CUTEst group, with the common target and
budgets. Every setting and failure is reported. Comparisons use each family's
primary setting as reference and distinguish joint and exclusive successes.
The study varies XR's initial memory; the fixed-memory ablation separately
examines its cap.

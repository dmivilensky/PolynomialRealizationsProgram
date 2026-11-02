# Experiments of Section 9

Reproduces every number and Figure 1 of Section 9 ("Numerical Experiments") of
*Chebyshev-Exact Acceleration under Hessian Variation, I: Sine–Jacobi Method*.

Requirements: Python ≥ 3.10, numpy, networkx, matplotlib
(with a LaTeX installation for `text.usetex`; the figure uses Latin Modern).

```
python3 run_all.py pred        # predictions only, before any simulation      ~5 s
python3 run_all.py             # predictions + all measurements                ~1 CPU-hour
python3 analyze.py             # summaries, fits, bootstrap -> results/summary.json
python3 plots.py               # ../fig_experiments.pdf
```

`python3 run_all.py <kind>` runs one kind and writes `results/raw_<kind>.npy`.

## What is compared

Four realizations of the same Chebyshev polynomial p_N^⋆, one gradient per step:
the semi-iterative method (`pref`), the sine–Jacobi method (`sine`), the Jacobi
method with weights w_j ∝ sin^{1/2} θ_j on the Chebyshev nodes (`quarter`, the point
t = 1/4 of the path w_j ∝ sin^{2t} θ_j of Lemma 6.1, built by Lanczos in
`common.path_jacobi`), and gradient descent with Chebyshev stepsizes in the
fractal (Lebedev–Finogenov) order (`gd`, N = 2^k). Without Hessian variation all
four return the same x_N. Figure 1 shows the error after one block relative to the
error of the same block without variation (1 = the variation does not matter).

## Kinds and parameters

| kind | instance | what is measured |
|---|---|---|
| `energy` | f(u) = ½uᵀAu + ¼Σu_i⁴ − 100Σu_i, A the Dirichlet Laplacian on 63 interior points of (0,1); ‖u⋆‖ = 27.9, κ(H⋆) = 283; x_0 = u⋆ + r_0 v | exact runs: ‖e_N‖ and ‖e_N − p_N^⋆(H⋆)e_0‖ for N = 64, 16 values of r_0 from 10⁻² to 30, 21 random unit directions v (Figure 1(a) uses the first); and ‖e_N − p_N^⋆e_0‖/r_0² at r_0 ∈ {10⁻³, 3·10⁻³, 10⁻²}, N = 16, …, 256, for the slowest eigenvector and a random direction, extrapolated to r_0 → 0 and compared with ‖Z(v)‖ |
| `gossip_scan` | ring of six 8-cliques (48 nodes, κ = 99), barbell of two 12-cliques (24 nodes, κ = 96), random geometric graph (60 nodes, radius 0.25, κ = 60), 8×8 grid (κ = 51); unit weights; each link fails independently with probability p in every step, surviving weights divided by 1−p; e_0 uniform on the unit sphere of 1^⊥ in each run | mean squared error E‖e_N‖² and excess E‖e_N − p_N^⋆e_0‖² after N = 32 steps, p = 10⁻⁵, 10^-4.5, …, 10⁻¹, 10⁵ runs per point, all four methods (Figure 1(b) shows the ring of cliques) |
| `gossip` | same graphs | excess at p ∈ {10^-4.5, 10⁻⁴, 10^-3.5}, N = 8, 16, 24, 32, 10⁵ runs, `pref`, `sine`, `quarter`; divided by σ² = p/(1−p) and extrapolated to p → 0 by weighted least squares in σ²; compared with Γ |
| `gossip_gd` | same graphs | the same for `gd` against `pref` at p ∈ {10⁻⁵, 10^-4.5, 10⁻⁴} (gradient descent leaves the first-order range earlier), N = 8, 16, 32, 3·10⁵ runs |

Predictions (Corollary 8.1) are computed from the eigendecomposition of the
reference Hessian only and are written to `results/pred.json` before any
simulation: for gossip, E‖p_N^⋆(L)e_0‖² and Γ, so that the predicted mean squared
error is E‖p_N^⋆(L)e_0‖² + p/(1−p)·Γ (the cross term vanishes because E e_N = p_N^⋆(L)e_0);
for the energy, p_N^⋆(H⋆)v and Z(v), so that the predicted error is
‖r_0 p_N^⋆(H⋆)v + r_0² Z(v)‖.

Seeds are derived from the specification (kind, graph, N, p), so the methods share
the random numbers (link failures and initial errors) and all numbers are
reproducible bit for bit on a given platform.

## Files

| file | content |
|---|---|
| `common.py` | coefficients of the four realizations, residual polynomials r_s, tail functions G_{N,s+1} (O(N) backward recurrence), `path_jacobi` |
| `models.py` | the four graphs and the energy |
| `predict.py` | E‖p_N^⋆e_0‖² and Γ for gossip (isotropic e_0), Z(v) and p_N^⋆(H⋆)v for the energy |
| `simulate.py` | Monte Carlo of gossip with link failures; exact runs on the energy |
| `run_all.py` | experiment specification and runner |
| `analyze.py` | scan summaries (95% intervals), extrapolation to zero noise, paired bootstrap |
| `plots.py` | Figure 1 |
| `results/pred.json`, `results/summary.json` | predictions and summaries used in the paper |

# Chebyshev-exact acceleration experiments

Numerical experiments for
[Chebyshev-Exact Acceleration under Gradient Variation](../bezout.pdf).
Python 3.11 or newer, NumPy and Matplotlib are required.

## Run

```sh
cd bezout-code
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B -m unittest discover -s tests -v
./run.sh --trials 256
./run.sh                 # full experiment, 2048 trials
```

`run.sh` uses `.venv/bin/python` when available, otherwise `python3`.
Predictions are saved before simulation. Individual stages can be run with
`./run.sh pred`, `./run.sh additive` and `./run.sh variation`.
Run `analyze.py` and `plots.py` with the same Python environment to rebuild
summaries and figures from saved results.

## Models and methods

**Distributed ridge regression.** The 64-dimensional Hessian is
`H = mu I + (1-mu) vv^T`, with `v = 1/sqrt(64)` and four workers.
The initial error has squared energy 0.9 in the weak eigenspace and 0.1
along v. Each worker rounds its gradient with subtractive uniform dither;
step `h = sigma sqrt(12 workers / dimension)` gives averaged covariance
`sigma^2 I / dimension`. The condition numbers are 100 and 10,000,
with `sigma / mu = 0.3`.

Methods: Flat, Prefix, LF/fractal, DFB and M-ASG. DFB averages all N+1
iterates, including the initial point, with step 1/L and momentum one.
M-ASG uses p=1 and first-stage length floor(N/2). The MSE predictions
include each method's own terminal bias.

**Coupled cycles.** Two cycles of 16 vertices share a varying inter-network
channel. On the antisymmetric subspace, the reference spectrum spans
`[1/kappa, 1]`. The initial signal has squared amplitude 0.475 in each
endpoint mode and total energy 0.05 across the interior modes.
Independent channel signs have amplitude `delta = 0.01 mu`.
The condition numbers are 10,000 and 40,000.

Methods: Balanced, Prefix, LF/fractal and sine–Jacobi. All have the same
nominal terminal. The signal matrix has entries
`T[j,s] = a[j] Phi[s](lambda[j]) pi[s](lambda[j])`.
Its largest singular value predicts local temporal-energy gain;
`delta^2 ||T||_F^2` is the leading noise variance. Simulations execute the
full perturbed oracle, while deterministic gain measurements differentiate
the actual iteration.

Both experiments use horizons
`64,128,256,320,384,512,640,768,960,1024` and a denser prediction grid.
LF runs only at dyadic horizons. Every method starts afresh at each horizon.
The problem and random-tape seeds are fixed in `models.py` and `run_all.py`.
Methods share each trial's random tape; dither errors can differ because
their queried gradients differ.

## Outputs

- `results/pred.json`: parameters and finite predictions.
- `results/raw_additive.npz`, `results/raw_variation.npz`: trial arrays.
- `results/summary.json`, `results/report.md`: ratios and paired-bootstrap intervals.
- `figures/additive.pdf`: terminal MSE and shared-energy additive gain.
- `figures/variation.pdf`: local channel gain and finite-noise variance.

All plotted quantities are divided by Prefix at the same instance and horizon.
Statistical markers have 95% paired-bootstrap intervals. The variation figure
shows LF separately on logarithmic axes; its first-variation ratios are
independent of kappa in this commuting channel model. Full terminal MSE is
saved separately from variance around the nominal terminal.

## Implementation and checks

`common.py` contains the iterations, physical responses and O(N) scalar
preparation. Flat/Balanced coefficients use 80-digit standard-library Decimal
arithmetic, then float64 vector iterations. Balanced evaluates the normalized
Q,W recurrence with compensated terminal accumulation.

The tests compare the iterations with independent exact rational histories,
check physical impulses and oracle counts, terminal polynomials, ridge data
and dither covariance, cycle spectra, channel derivatives, root-order
invariance and N=1024 runs. Separate rational tests cover the signed
odd-horizon four-corner bounds and Balanced equality.

The formulas, method references and finite-comparison derivations are in
the accompanying article, especially Appendix D.

# Generating the article figures and tables

The article reads only `artifacts/paper/figures` and `artifacts/paper/tables`.
The publication script copies these files byte for byte from completed study
outputs. Histories, reports and other diagnostic figures remain local.

## Generate

From `krylov-code`, after the main, settings, reference and local studies:

```sh
"$XR_PYTHON" -B scripts/render_release.py --output artifacts/run
"$XR_PYTHON" -B scripts/release_audit.py --output artifacts/run
"$XR_PYTHON" -B scripts/paper_assets.py --run artifacts/run
```

`render_release.py` validates completed histories and renders all four studies
without executing optimizers. The audit checks scheduled jobs, data receipts,
actual targets, source identities and native modules. `paper_assets.py`
requires all article inputs before copying any file. Its `--run` option
selects another completed output directory.

## Figures

| File under `artifacts/paper/figures` | Content |
|---|---|
| `controlled.pdf` | Quadratic trajectory and complete perturbation-grid heatmap. |
| `cutest_gradients.pdf` | Four CUTEst cohorts, ordinary and empirical-logit gradient profiles. |
| `cutest_time.pdf` | The corresponding elapsed-time profiles. |
| `libsvm.pdf` | Gradient and time profiles for all 24 logistic objectives. |
| `local.pdf` | Every accepted iterate of two fixed full-memory trajectories. |

## Tables

| File under `artifacts/paper/tables` | Content |
|---|---|
| `ablations.tex` | Six one-factor changes and their baseline. |
| `settings_summary.tex` | Memory sensitivity with paired ratios and exclusive successes. |
| `bfgs_reference.tex` | Full-matrix BFGS-SP and primary methods. |
| `tighter_target.tex` | Relative gradient tolerance `1e-10`. |
| `local_summary.tex` | Full-memory target, work and first full window. |
| `libsvm_datasets.tex` | Dataset dimensions and storage. |
| `libsvm_comparisons.tex` | Paired costs by regularization. |

The preset table is maintained directly in the article. Constant generated
table columns are stated in captions. Values are computed from observations;
no plot-specific rescaling or manual numerical correction is applied.

From the enclosing repository, use e.g.

```tex
\includegraphics[width=\linewidth]{krylov-code/artifacts/paper/figures/controlled.pdf}
\input{krylov-code/artifacts/paper/tables/ablations.tex}
```

Typeset the manuscript from the enclosing repository:

```sh
python3 -m Tools.Typesetting.Build krylov.tex
```

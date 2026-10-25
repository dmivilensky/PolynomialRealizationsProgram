"""Build all fourteen figures of the paper into figures/pdf/ (PDF; another folder can be set with the
environment variable HB_FIGURES) and data/ (PNG previews).

Usage: python make_all.py [--data]

The figure data are read from data/. They are recomputed when missing or when --data is given:
phase_data.py (about two minutes), gap_data.py for the first level at kappa = 100 (about an hour on one
core), gap_refine.py, and the data programs of Figures 7, 8, 11 and
13 (several hours on one core). Part I curves are computed by part1/rate.py and cached in
data/rates.npz and data/boundary_t.npz.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / 'data'

FIGURES = ('fig_rates', 'fig_boundary', 'fig_spectra', 'fig_thomae', 'fig_phase', 'fig_regions', 'fig_gapchart',
           'fig_tongues', 'fig_lattice', 'fig_level1', 'fig_staircase', 'fig_modelock', 'fig_plateau', 'fig_edges')


def run(*args):
    print('$', ' '.join(args), flush=True)
    subprocess.run([sys.executable, *args], cwd=HERE, check=True)


def missing(*names):
    return not all((DATA / n).exists() for n in names)


def main():
    fresh = '--data' in sys.argv
    DATA.mkdir(exist_ok=True)
    if fresh or missing(*(f'phase_{k}.npz' for k in (2, 10, 100, 1000))):
        run('phase_data.py')
    if fresh or missing('gap_100.npz'):
        run('gap_data.py', '100', '0.40', '0.93', '0.05', '900', '260')
    if fresh or missing('gap_100_hi.npz'):
        run('gap_data.py', '100', '0.38', '0.66', '0.16', '700', '320', '_hi')
    if fresh or missing('gap_100_refined.npz', 'gap_100_hi_refined.npz'):
        run('gap_refine.py')
    if fresh or missing('gapchart_l1.1.json'):
        run('data_gapchart.py', '4', 'l1.1', '36', 'gapchart_l1.1.json', '70')
    if fresh or missing('gapchart_200.json'):
        run('data_gapchart.py', '4', '200', '36', 'gapchart_200.json', '70')
    if fresh or missing('gapchart_2000.json'):
        run('data_gapchart.py', '4', '2000', '40', 'gapchart_2000.json', '70')
    if fresh or missing('tongues_0.995.json'):
        run('data_tongues.py', '0.995', '1.37', '2.03', '133', '60')
    if fresh or missing('st150a.json'):
        run('data_staircase.py', '150', '0.606', '0.62', '71', 'st150a.json')
    if fresh or missing('st150b.json'):
        run('data_staircase.py', '150', '0.6202', '0.634', '70', 'st150b.json')
    if fresh or missing('plateau_2_9.json'):
        run('data_plateau.py')
        run('data_plateau_image.py')
    if fresh:
        for f in ('rates.npz', 'boundary_t.npz'):
            (DATA / f).unlink(missing_ok=True)
    for script in FIGURES:
        run(script + '.py')
    print('ALL FIGURES BUILT')


if __name__ == '__main__':
    main()

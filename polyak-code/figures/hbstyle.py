"""Plotting style of Figures 7, 8 and 11-14; save_figure writes figures/pdf/NAME.pdf
(or HB_FIGURES/NAME.pdf) and the preview data/NAME.png."""
import os
from pathlib import Path
import matplotlib as mpl
mpl.use('Agg')
import matplotlib.pyplot as plt
from plot_fonts import register_fonts
C = dict(green='#71ccac', lgreen='#ccece1', yellow='#f4ca72', blue='#8fb8e9', lblue='#bad3f1',
         red='#e24847', lred='#f8d2d1', grey='#e3e2de', ink='#3d3c39', black='#0b0b0b',
         cblue='#2a78d6', cgreen='#1baf7a', violet='#4a3aa7', orange='#eb6834', pink='#e77aa3',
         dgrey='#8a8984')
def setup():
    register_fonts()
    mpl.rcParams.update({
        'font.family': 'serif', 'font.serif': ['Latin Modern Roman', 'LM Roman 10', 'DejaVu Serif'], 'mathtext.fontset': 'cm',
        'axes.labelpad': 2, 'axes.titlepad': 3,
        'xtick.major.pad': 2, 'ytick.major.pad': 2,
        'legend.borderaxespad': 0.25, 'legend.labelspacing': 0.25,
        'font.size': 8, 'axes.titlesize': 8.5, 'axes.labelsize': 8, 'xtick.labelsize': 7,
        'ytick.labelsize': 7, 'legend.fontsize': 7, 'axes.linewidth': 0.6,
        'xtick.major.width': 0.5, 'ytick.major.width': 0.5, 'xtick.major.size': 2.5,
        'ytick.major.size': 2.5, 'axes.edgecolor': C['ink'], 'axes.labelcolor': C['ink'],
        'xtick.color': C['ink'], 'ytick.color': C['ink'], 'text.color': C['ink'],
        'axes.spines.top': True, 'axes.spines.right': True, 'pdf.fonttype': 42,
        'axes.titlelocation': 'left', 'axes.unicode_minus': False})


ROOT = Path(__file__).resolve().parents[1]
OUT = Path(os.environ.get('HB_FIGURES', ROOT / 'figures' / 'pdf'))


def save_figure(fig, name):
    OUT.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUT / f'{name}.pdf', bbox_inches='tight', pad_inches=0.02)
    fig.savefig(ROOT / 'data' / f'{name}.png', dpi=200, bbox_inches='tight', pad_inches=0.02)

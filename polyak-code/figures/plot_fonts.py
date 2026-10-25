"""Register optional publication fonts without depending on a TeX installation."""
import os
from pathlib import Path
from matplotlib import font_manager


def register_fonts():
    directories = [Path('/usr/share/texmf/fonts/opentype/public/lm')]
    if os.environ.get('HB_FONT_DIRECTORY'):
        directories.append(Path(os.environ['HB_FONT_DIRECTORY']))
    for directory in directories:
        for path in directory.glob('lmroman10-*.otf'):
            font_manager.fontManager.addfont(str(path))

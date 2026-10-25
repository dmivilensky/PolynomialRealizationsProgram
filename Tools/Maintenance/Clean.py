"""Remove disposable artifacts while preserving the distributable proof sources.

Reproducible Polyak inputs from the local polyak-code archives are disposable,
including the generated Boundary inputs. Keep handwritten proofs, generators,
source descriptors, tools-owned converter registrations, other packages' checked-in witnesses, the pinned
manifest and article PDFs. Remove Lake's entire cache, including downloads,
extraction, reports and compiled proofs. Run --dry-run to inspect the list.
The next verification prepares Polyak inputs again from its pinned source.
"""
import argparse
from pathlib import Path
import shutil

from Tools.Certificates.PolyakOutputs import EXPECTED as POLYAK_OUTPUTS
from Tools.Certificates.PolyakPartIIOutputs import EXPECTED as POLYAK_PARTII_OUTPUTS

ROOT = Path(__file__).resolve().parents[2]


def disposable_paths():
    """
    Select known artifact roots and incidental OS/Python files, never Git data.

    Walking excludes .git and symlinks. An entire .lake directory is selected once instead of
    enumerating its millions of dependent artifact files. Unknown files are preserved rather
    than guessed to be disposable.
    """
    roots = [ROOT / name for name in (".lake", ".VSCodeCounter")]
    selected = [path for path in roots if path.exists() or path.is_symlink()]

    for name in sorted(POLYAK_OUTPUTS | POLYAK_PARTII_OUTPUTS):
        path = ROOT / name
        # Never inspect or delete an output through a symlinked parent directory.
        if any((ROOT / parent).is_symlink() for parent in Path(name).parents
               if parent != Path(".")):
            continue
        if path.exists() or path.is_symlink():
            selected.append(path)

    def visit(folder):
        """
        Walk source directories without following symlinks or descending into .git or selected
        cache roots. Only known incidental artifact names are selected.
        """
        for path in folder.iterdir():
            if path.name == ".git" or path in roots:
                continue
            if path.name in (".DS_Store", "__pycache__") or path.suffix == ".pyc":
                selected.append(path)
            elif path.is_dir() and not path.is_symlink():
                visit(path)

    visit(ROOT)
    return sorted(selected)


def clean(path):
    """
    Unlink a selected file/symlink or recursively remove a selected directory.

    The lexical containment check protects the repository parent; symlinks are unlinked without
    following them to any outside directory.
    """
    path.relative_to(ROOT)
    if path == ROOT or ".git" in path.relative_to(ROOT).parts:
        raise ValueError(f"Protected path: {path}")
    if path.is_symlink() or not path.is_dir():
        path.unlink()
    else:
        shutil.rmtree(path)


def main():
    """
    Show or delete the same explicit artifact list; no generator is executed.
    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true", help="List paths without deleting them")
    args = parser.parse_args()
    for path in disposable_paths():
        print(("Would remove " if args.dry_run else "Removing ") + str(path.relative_to(ROOT)))
        if not args.dry_run:
            clean(path)


if __name__ == "__main__":
    main()

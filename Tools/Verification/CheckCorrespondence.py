"""Check local showcase links, proof placeholders and import coverage without reading paper sources."""
import argparse
import re

from .Project import lean_code, name_parts, select_projects, workspace_sources


def imports(path):
    """Extract imports after masking nested comments and strings without changing positions."""
    source = lean_code(path.read_text())
    return [name for match in re.finditer(
        r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", source, re.M)
        for name in match[1].split() if name not in {"all", "meta"}]


def check_showcase(project):
    """Compare the optional hand-maintained table and showcase, checking only local Lean links."""
    article = project.directory / "Article.lean"
    table = project.directory / "ArticleMap.md"
    declarations = (re.findall(r"^#check @?([^\s]+)\s*$", lean_code(article.read_text()), re.M)
                    if article.is_file() else [])
    if not table.exists():
        return 0, len(declarations)
    if not article.is_file():
        raise ValueError(f"{project.relative}: ArticleMap.md requires an Article.lean showcase")
    declared_names = [name_parts(name) for name in declarations]
    listed = []
    labels = []
    for row in table.read_text().splitlines():
        if not row.startswith("| ") or row.startswith(("| Article |", "| ---")):
            continue
        columns = row.split("|")
        labels.append(columns[1].strip())
        for name, link in re.findall(r"\[([^\]]+)\]\(([^)]+\.lean)\)", columns[2]):
            if not (project.directory / link).is_file():
                raise ValueError(f"Broken declaration file link: {link}")
            parts = name_parts(name)
            listed.append(parts if parts in declared_names else (*project.parts, *parts))
    if listed != declared_names:
        raise ValueError(f"{project.relative}: correspondence table differs from the ordered showcase")
    return len(labels), len(declarations)


def check(project):
    """Check one arbitrary package's own sources, optional showcase and complete import closure."""
    if not hasattr(project, "directory"):
        project = select_projects([project])[0]
    labels, declarations = check_showcase(project)
    paths = project.sources
    for path in paths:
        executable = lean_code(path.read_text())
        if re.search(r"\b(sorry|admit|native_decide)\b", executable):
            raise ValueError(f"Unfinished or native-trust proof: {path}")
    sources = workspace_sources(project.workspace)
    by_parts = {name_parts(name): path for name, path in sources.items()}
    reachable = set()
    pending = [(*project.parts, "Check")]
    while pending:
        parts = pending.pop()
        if parts in reachable or parts not in by_parts:
            continue
        reachable.add(parts)
        pending.extend(name_parts(name) for name in imports(by_parts[parts]))
    missing = sorted(project.source_module(path) for path in paths
                     if name_parts(project.source_module(path)) not in reachable)
    if missing:
        raise ValueError(f"Sources outside the full check: {missing}")
    print(f"{project.relative}: {labels} table entries, {declarations} showcase references, "
          f"{len(paths)} imported sources.")


def main():
    """Select directories or all discovered packages without maintaining an article list."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", nargs="*", help="Source directories, or all (default)")
    args = parser.parse_args()
    try:
        for project in select_projects(args.directory):
            check(project)
    except (OSError, ValueError) as error:
        parser.exit(1, f"Source check failed: {error}\n")


if __name__ == "__main__":
    main()

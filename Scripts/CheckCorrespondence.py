"""Check article tables, ordered showcases, source annotations and complete import coverage."""
from pathlib import Path
import re
import sys
from CheckDocumentation import check_file

ROOT = Path(__file__).resolve().parent.parent
PAPERS = ("2606.16671v2", "2610.05164v2")


def imports(path):
    """
    Extract direct import names after removing block comments, for the owned-source coverage
    graph.
    """
    source = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
    return [name for line in source.splitlines() if line.startswith("import ")
            for name in line.split()[1:]]


def module(path):
    """
    Map a source path to its Lean module name, treating each dotted article stem as one escaped
    identifier.
    """
    parts = path.relative_to(ROOT).with_suffix("").parts
    return ".".join((f"«{parts[0]}»" if parts[0] in PAPERS else parts[0], *parts[1:]))


def check(paper):
    """
    Match the ordered article inventory, clickable correspondence table and showcase
    references. Also require article/proof-role headers, reject unfinished/native-trust proofs
    and check complete import coverage.
    """
    folder = ROOT / paper
    article = (folder / "Article.lean").read_text()
    declarations = re.findall(r"^#check @([^\s]+)$", article, re.M)
    listed = []
    labels = []
    for row in (folder / "ArticleMap.md").read_text().splitlines():
        if not row.startswith("| ") or row.startswith(("| Article |", "| ---")):
            continue
        columns = row.split("|")
        labels.append(columns[1].strip())
        for name, link in re.findall(r"\[([^\]]+)\]\(([^)]+\.lean)\)", columns[2]):
            if not (folder / link).is_file():
                raise ValueError(f"Broken declaration file link: {link}")
            listed.append(name if name.startswith("«") else f"«{paper}».{name}")
    if listed != declarations:
        raise ValueError(f"{paper}: correspondence table differs from the ordered showcase")
    # Check the complete inventory against the labeled results in the article.
    required = (
        ["Lemma 1.1", "Definition 1.2", "Proposition 1.3", "Theorem 1.4",
         "Theorem 2.1", "Theorem 2.2", "Theorem 3.1", "Theorem 4.1", "Theorem 4.2",
         "Theorem 4.3", "Corollary 4.4", "Algorithm 1", "Algorithm 2", "Theorem 5.1",
         "Theorem 5.2", "Corollary 5.3", "Corollary 5.4", "Remark 5.5", "Section 6",
         "Appendix A", "Lemma B.1", "Theorem C.1", "Appendix D", "Theorem E.1",
         "Lemma E.2", "Theorem E.3", "Lemma E.4", "Lemma E.5", "Lemma E.6", "Lemma E.7",
         "Lemma E.8", "Appendix F"]
        if paper == PAPERS[0] else
        ["Theorem 1.1", "Theorem 1.2", "Definition 1", "Theorem 2.1", "Theorem 2.2",
         "Corollary 1", "Proposition 1", "Theorem 2.3", "Theorem 2.4", "Theorem 2.5",
         "Definition 2", "Proposition 2", "Definition 3", "Theorem 3.1", "Proposition 3",
         "Definition 4", "Proposition 4", "Theorem 3.2", "Proposition 5", "Proposition 6",
         "Theorem 3.3", "Definition 5", "Proposition 7", "Definition 6", "Theorem 3.4",
         "Proposition 8", "Theorem 3.5", "Definition 7", "Definition 8", "Theorem 3.6",
         "Section 4.1", "Proposition 9", "Corollary 2", "Proposition 10", "Theorem 5.1",
         "Definition 9", "Theorem 5.2", "Proposition 11", "Corollary 3", "Theorem 6.1",
         "Hypothesis 1", "Lemma 1", "Lemma 2", "Lemma 3", "Theorem A.1", "Lemma 4",
         "Lemma 5", "Lemma 6", "Lemma 7", "Proposition 12", "Lemma 8", "Lemma 9",
         "Lemma 10", "Definition 10", "Lemma 11", "Lemma 12", "Lemma 13", "Lemma 14",
         "Lemma 15", "Theorem E.1", "Lemma 16", "Lemma 17", "Lemma 18", "Lemma 19",
         "Lemma 20", "Lemma 21", "Lemma 22", "Lemma 23", "Lemma 24", "Lemma 25",
         "Proposition 13", "Lemma 26"]
    )
    if labels != required:
        raise ValueError(f"{paper}: article statement inventory/order changed")
    paths = [*folder.rglob("*.lean"), ROOT / (paper + ".lean")]
    for path in paths:
        check_file(path)
        source = path.read_text()
        header = re.search(r"/-!(.*?)-/", source, re.S)
        if not header or paper not in header[1]:
            raise ValueError(f"Missing article correspondence: {path}")
        if not re.search(r"\b(Use|Result|Interface):", header[1]):
            raise ValueError(f"Missing proof role: {path}")
        if re.search(r"\b(sorry|admit|native_decide)\b", re.sub(r"/-.*?-/", "", source, flags=re.S)):
            raise ValueError(f"Unfinished or native-trust proof: {path}")
        executable = re.sub(r"/-.*?-/|--[^\n]*", "", source, flags=re.S)
        executable = re.sub(r'"(?:\\.|[^"\\])*"', '""', executable)
        if re.search(r"(?<!«)(?:2606\.16671v2|2610\.05164v2)(?!»)", executable):
            raise ValueError(f"Unquoted article stem inside Lean code: {path}")
    sources = {module(p): p for stem in PAPERS
               for p in [*(ROOT / stem).rglob("*.lean"), ROOT / (stem + ".lean")]}
    reachable = set()

    def visit(name):
        """
        Traverse direct owned imports once to identify every source reached by the article's
        complete verification entry point.
        """
        if name in reachable or name not in sources:
            return
        reachable.add(name)
        for dep in imports(sources[name]):
            visit(dep)

    visit(f"«{paper}».Check")
    missing = sorted(module(p) for p in paths if module(p) not in reachable)
    if missing:
        raise ValueError(f"Sources outside the full check: {missing}")
    print(f"{paper}: {len(labels)} ordered entries, {len(declarations)} references, "
          f"{len(paths)} annotated/imported sources.")


if __name__ == "__main__":
    for paper in sys.argv[1:] or PAPERS:
        if paper not in PAPERS:
            raise ValueError("Unknown article: " + paper)
        check(paper)

"""Publication copies retain measured bytes and require all article inputs."""

import hashlib
import importlib.util
from pathlib import Path

import pytest


@pytest.fixture
def publisher():
    path = Path(__file__).resolve().parents[1] / "scripts/paper_assets.py"
    spec = importlib.util.spec_from_file_location("paper_assets_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def inputs(publisher, directory):
    for target, source in publisher.ASSETS.items():
        path = directory / source
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"%PDF-1.5\n" + target.encode() if path.suffix == ".pdf"
                         else b"\\begin{table}\n" + target.encode())


def test_publication_preserves_bytes_and_excludes_unrelated_outputs(publisher, tmp_path):
    run, output = tmp_path / "run", tmp_path / "paper"
    inputs(publisher, run)
    (run / "history.jsonl").write_text('"measurement log"\n')
    result = publisher.publish(run, output)
    copied = {str(p.relative_to(output)) for p in output.rglob("*") if p.is_file()}
    assert copied == set(publisher.ASSETS)
    for relative, original in publisher.ASSETS.items():
        data = (run / original).read_bytes()
        assert (output / relative).read_bytes() == data
        assert result[relative] == hashlib.sha256(data).hexdigest()


@pytest.mark.parametrize("invalid", ["missing", "invalid-pdf"])
def test_incomplete_or_invalid_inputs_do_not_publish_partial_output(publisher, tmp_path, invalid):
    run, output = tmp_path / "run", tmp_path / "paper"
    inputs(publisher, run)
    source = run / publisher.ASSETS["figures/local.pdf"]
    if invalid == "missing":
        source.unlink()
    else:
        source.write_text("A failed generator did not produce a PDF.")
    with pytest.raises((FileNotFoundError, ValueError)):
        publisher.publish(run, output)
    assert not output.exists()

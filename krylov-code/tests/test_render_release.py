"""Release rendering changes presentation only and never executes an optimizer."""

import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest


@pytest.fixture
def renderer():
    path = Path(__file__).resolve().parents[1] / "scripts/render_release.py"
    spec = importlib.util.spec_from_file_location("xr_render_release_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_reproduction_correction_preserves_outcomes_pins_and_other_shell_blocks(renderer):
    before = (
        "# Settings\n\nNumerical ratio: 1.234; 15/16 solved.\n"
        "```sh\nold unrelated example artifacts/full\n```\n\n"
        "## Reproduction\n\n```sh\npython old --workers 8\n```\n\n"
        "Scientific SHA256: `untouched-signed-input`.\n"
        "## Other section\n\n```sh\nnever touch this\n```\n"
    )
    commands = ["python -B scripts/render_release.py --output artifacts/native-expanded"]
    after = renderer._reproduction_block(before, commands)
    assert after == before.replace("python old --workers 8", commands[0])
    assert renderer._reproduction_block(after, commands) == after
    with pytest.raises(ValueError, match="Reproduction"):
        renderer._reproduction_block("Missing the expected heading", commands)


def test_complete_wrapper_uses_render_apis_only_and_preserves_measured_inputs(
    renderer, tmp_path, monkeypatch
):
    from xrbench import study

    monkeypatch.setattr(renderer, "ROOT", tmp_path)
    for name in renderer.PRODUCERS:
        path = tmp_path / "scripts" / (name + ".py")
        path.parent.mkdir(exist_ok=True)
        path.write_text("# Frozen measured producer; unchanged.\n")
    base = tmp_path / "artifacts/native-expanded"
    for phase in ("full", "settings", "supplement", "local"):
        logs = base / phase if phase == "full" else base / phase / "logs"
        logs.mkdir(parents=True)
        (logs / "manifest.json").write_text("{}\n")
        (logs / "history.jsonl").write_text('{"measured":true}\n')
    before = renderer._fingerprints(base)
    calls = []

    def fail_if_executed(*args, **kwargs):
        raise AssertionError("A render-only wrapper invoked scientific execution")

    def producer(phase):
        def render(folder, *args):
            assert folder == base / phase
            calls.append(phase)
            (folder / "REPORT.md").write_text(
                "# Measured results\n\nRatio 1.125; all original outcomes retained.\n\n"
                "## Reproduction\n\n```sh\npython old --main artifacts/full --workers 8\n```\n\n"
                "Input SHA256: `frozen-source-pin`.\n"
            )
            return {"rendered": phase}

        return SimpleNamespace(render=render, execute=fail_if_executed, run=fail_if_executed)

    modules = {
        name: producer(phase)
        for name, phase in zip(renderer.PRODUCERS, ("settings", "supplement", "local"))
    }
    inputs = dict(
        main={"jobs": [], "aliases": [], "methods": {}, "problems": []},
        rows=[],
        settings={"workers": 1},
        supplement={"workers": 1},
        local={},
        local_rows=[],
        scripts=modules,
    )
    monkeypatch.setattr(renderer, "_inputs", lambda _: inputs)

    def main_render(rows, output, **kwargs):
        assert rows == [] and output == base / "full"
        calls.append("full")
        return {"rendered": "full"}

    monkeypatch.setattr(study, "render", main_render)
    result = renderer.render_release(base)
    assert calls == ["full", "settings", "supplement", "local"]
    assert result["render_only"] and result["frozen_inputs_unchanged"]
    assert renderer._fingerprints(base) == before
    supplement = (base / "supplement/REPORT.md").read_text()
    assert "--workers 1" in supplement and "--workers 8" not in supplement
    assert "--main artifacts/native-expanded/full" in supplement
    assert "--output artifacts/native-expanded/supplement" in supplement
    assert "scripts/render_release.py --output artifacts/native-expanded" in supplement
    for phase in ("settings", "supplement"):
        text = (base / phase / "REPORT.md").read_text()
        assert "Ratio 1.125; all original outcomes retained" in text
        assert "`frozen-source-pin`" in text


def test_preflight_job_completeness_rejects_missing_and_duplicate_observations(renderer):
    with pytest.raises(ValueError, match="every scheduled job"):
        renderer._complete_jobs(
            [{"job_id": "one"}], {"jobs": [{"id": "one"}, {"id": "two"}]}, "test"
        )
    with pytest.raises(ValueError, match="duplicate"):
        renderer._complete_jobs(
            [{"job_id": "one"}, {"job_id": "one"}], {"jobs": [{"id": "one"}]}, "test"
        )

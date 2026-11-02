import json

import pytest

from xrbench.campaign import campaign_writer_lock, recover_history_tail


def test_interrupted_append_preserves_completed_results(tmp_path):
    path = tmp_path / "history.jsonl"
    completed = b'{"job_id":"saved","success":false}\n'
    tail = b'{"job_id":"unfinished"'
    path.write_bytes(completed + tail)
    recover_history_tail(path)
    assert path.read_bytes() == completed
    logs = list((tmp_path / "logs").glob("interrupted-tail-*.log"))
    assert len(logs) == 1 and logs[0].read_bytes() == tail


def test_complete_final_record_kept_without_its_newline(tmp_path):
    path = tmp_path / "history.jsonl"
    value = dict(job_id="saved", success=False)
    path.write_text(json.dumps(value))
    recover_history_tail(path)
    assert path.read_text() == json.dumps(value) + "\n"
    assert not (tmp_path / "logs").exists()


def test_corruption_before_last_append_is_not_erased(tmp_path):
    path = tmp_path / "history.jsonl"
    original = b'{bad}\n{"job_id":'
    path.write_bytes(original)
    with pytest.raises(ValueError):
        recover_history_tail(path)
    assert path.read_bytes() == original


def test_writer_lock_covers_direct_entry_points(tmp_path):
    with campaign_writer_lock(tmp_path):
        with pytest.raises(ValueError, match="writer lock"):
            with campaign_writer_lock(tmp_path):
                pytest.fail("Two writers acquired the same output")
    with campaign_writer_lock(tmp_path):
        pass

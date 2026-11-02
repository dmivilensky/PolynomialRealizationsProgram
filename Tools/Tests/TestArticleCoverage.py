"""Check reviewed maps and Lean showcases without manuscript inputs."""
from contextlib import redirect_stdout
import io
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

from Tools.Verification import ArticleCoverage


class ArticleMapReviewTests(unittest.TestCase):
    """Keep reviewed numbered and unnumbered entries aligned with Lean."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.directory = self.root / 'Example'
        self.directory.mkdir()
        self.proof = self.directory / 'Proof.lean'
        self.proof.write_text('theorem first : True := True.intro\n')
        self.article = self.directory / 'Article.lean'
        self.article.write_text('''import Example.Proof
/-! Article: Theorem 1.1 [thm:first]. First. -/
#check @Example.first
/-! Article: Lemma 1.3 [lem:second]. -/
#check @Example.second
/-! Article: Definition A.1 [def:third]. Third. -/
#check @Example.third
''')
        self.table = self.directory / 'ArticleMap.md'
        self.table.write_text('''# Correspondence
<!-- article-review -->
<!-- article-numbered-count: 3 -->
<!-- article-prose-count: 1 -->
| Article | Lean declarations | Meaning and exclusions |
| --- | --- | --- |
| Theorem 1.1 — First (`thm:first`) | [first](Proof.lean) | A. |
| Lemma 1.3 (`lem:second`) | [second](Proof.lean) | B. |
| Definition A.1 — Third (`def:third`) | [third](Proof.lean) | C. |

- `unnumbered` — Additional mathematics. [Proof](Proof.lean).
''')
        self.project = SimpleNamespace(workspace=self.root, directory=self.directory,
                                       relative='Example', parts=('Example',),
                                       sources=(self.proof, self.article))

    def check(self):
        with redirect_stdout(io.StringIO()):
            return ArticleCoverage.check(self.project, require_complete=True)

    def test_reviewed_inventory_matches_showcase(self):
        self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def test_review_needs_no_manuscript_files(self):
        original = Path.open

        def guarded_open(path, *args, **kwargs):
            if path.suffix == ".tex":
                raise AssertionError("Verification attempted to read a manuscript")
            return original(path, *args, **kwargs)

        with mock.patch.object(Path, "open", guarded_open):
            self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def test_jointly_deleting_a_map_row_and_showcase_block_is_rejected(self):
        self.table.write_text('\n'.join(line for line in self.table.read_text().splitlines()
                                        if not line.startswith('| Lemma')))
        raw = self.article.read_text().replace(
            '/-! Article: Lemma 1.3 [lem:second]. -/\n#check @Example.second\n', '')
        self.article.write_text(raw)
        with self.assertRaisesRegex(ValueError, 'numbered claim inventory'):
            self.check()

    def test_duplicate_reviewed_labels_and_numbers_are_rejected(self):
        original = self.table.read_text()
        for changed in [original.replace('lem:second', 'thm:first'),
                        original.replace('Lemma 1.3', 'Lemma 1.1')]:
            with self.subTest(changed=changed):
                self.table.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'Duplicate reviewed claim'):
                    self.check()

    def test_review_marker_and_counts_are_required_for_complete_review(self):
        original = self.table.read_text()
        for changed in [original.replace('<!-- article-review -->', ''),
                        original.replace('<!-- article-numbered-count: 3 -->', ''),
                        original.replace('<!-- article-numbered-count: 3 -->',
                                         '<!-- article-numbered-count: 2 -->')]:
            with self.subTest(changed=changed):
                self.table.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'no article coverage review|claim inventory'):
                    self.check()

    def test_missing_reordered_or_relabelled_result_is_rejected(self):
        original = self.table.read_text()
        for changed in [original.replace('1.3', '1.2'),
                        original.replace('lem:second', 'lem:other'),
                        original.replace(' — First', ''),
                        '\n'.join(line for line in original.splitlines() if '| Lemma' not in line)]:
            with self.subTest(changed=changed):
                self.table.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'inventory differs|Showcase'):
                    self.check()

    def test_showcase_cannot_reference_different_declarations(self):
        self.article.write_text(self.article.read_text().replace('@Example.second', '@Example.other'))
        with self.assertRaisesRegex(ValueError, 'ordered showcase'):
            self.check()

    def test_showcase_numbers_and_labels_must_match_reviewed_order(self):
        self.article.write_text(self.article.read_text().replace('Lemma 1.3', 'Lemma 1.2'))
        with self.assertRaisesRegex(ValueError, 'Showcase comments differ'):
            self.check()

    def test_showcase_title_must_match_reviewed_map(self):
        self.article.write_text(self.article.read_text().replace(']. First.', ']. Another title.'))
        with self.assertRaisesRegex(ValueError, 'Showcase title differs'):
            self.check()

    def test_commented_out_signature_does_not_count_as_a_lean_check(self):
        self.article.write_text(self.article.read_text().replace(
            '#check @Example.second', '/-\n#check @Example.second\n-/'))
        with self.assertRaisesRegex(ValueError, 'ordered showcase'):
            self.check()

    def test_signatures_must_stay_in_their_own_numbered_block(self):
        raw = self.article.read_text()
        raw = raw.replace('#check @Example.first\n', '') + '#check @Example.first\n'
        # Retain the overall check order by moving every check to the last block.
        raw = '\n'.join(line for line in raw.splitlines() if not line.startswith('#check'))
        raw += '\n#check @Example.first\n#check @Example.second\n#check @Example.third\n'
        self.article.write_text(raw)
        with self.assertRaisesRegex(ValueError, 'inside article block'):
            self.check()

    def test_deleted_prose_obligation_cannot_pass(self):
        self.table.write_text(self.table.read_text().replace('- `unnumbered`', '- removed'))
        with self.assertRaisesRegex(ValueError, 'Unnumbered mathematics inventory'):
            self.check()

    def test_explicit_gap_cannot_be_certified_as_complete(self):
        self.table.write_text(self.table.read_text() + '\n<!-- article-unresolved: an implication -->\n')
        with self.assertRaisesRegex(ValueError, 'Incomplete article coverage'):
            self.check()

if __name__ == '__main__':
    unittest.main()

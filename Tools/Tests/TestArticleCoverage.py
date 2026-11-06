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

    def test_numbered_mathematical_remark_is_checked_in_source_order(self):
        self.table.write_text(self.table.read_text().replace(
            'Definition A.1', 'Remark A.1').replace('def:third', 'rem:third'))
        self.article.write_text(self.article.read_text().replace(
            'Definition A.1', 'Remark A.1').replace('def:third', 'rem:third'))
        self.assertEqual(self.check()['verified_numbered_claims'], 3)
        self.article.write_text(self.article.read_text().replace('Remark A.1', 'Remark A.2'))
        with self.assertRaisesRegex(ValueError, 'Showcase comments differ'):
            self.check()

    def test_review_needs_no_manuscript_files(self):
        original = Path.open

        def guarded_open(path, *args, **kwargs):
            if path.suffix.lower() in {".tex", ".pdf"}:
                raise AssertionError("Verification attempted to read a manuscript")
            return original(path, *args, **kwargs)

        with mock.patch.object(Path, "open", guarded_open):
            self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def use_topic_inventory(self):
        self.table.write_text(self.table.read_text().replace(
            '<!-- article-numbered-count: 3 -->', '<!-- article-topic-count: 3 -->').replace(
            'Theorem 1.1 — First', 'Topic — First').replace(
            'Lemma 1.3', 'Topic — Second').replace('Definition A.1 — Third', 'Topic — Third'))
        self.article.write_text(self.article.read_text().replace(
            'Theorem 1.1', 'Topic').replace('Lemma 1.3 [lem:second].',
            'Topic [lem:second]. Second.').replace('Definition A.1', 'Topic'))

    def test_topic_inventory_checks_signatures_without_manuscript_numbers(self):
        self.use_topic_inventory()
        self.assertEqual(self.check()['verified_topic_claims'], 3)
        self.article.write_text(self.article.read_text().replace('[lem:second]', '[lem:other]'))
        with self.assertRaisesRegex(ValueError, 'Showcase comments differ'):
            self.check()

    def test_topic_inventory_rejects_deletion_and_mixed_numbered_counts(self):
        self.use_topic_inventory()
        original = self.table.read_text()
        self.table.write_text('\n'.join(line for line in original.splitlines()
                                        if not line.startswith('| Topic — Second')))
        with self.assertRaisesRegex(ValueError, 'topic claim inventory'):
            self.check()
        self.table.write_text(original + '\n<!-- article-numbered-count: 3 -->\n')
        with self.assertRaisesRegex(ValueError, 'Mixed topic and numbered'):
            self.check()

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
                        original.replace('Lemma 1.3', 'Theorem 1.1')]:
            with self.subTest(changed=changed):
                self.table.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'Duplicate reviewed claim'):
                    self.check()

    def test_separate_theorem_and_lemma_counters_may_share_a_number(self):
        self.table.write_text(self.table.read_text().replace('Lemma 1.3', 'Lemma 1.1'))
        self.article.write_text(self.article.read_text().replace('Lemma 1.3', 'Lemma 1.1'))
        self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def test_supplementary_algorithms_have_distinct_labels_and_typed_entries(self):
        self.table.write_text(self.table.read_text().replace(
            'Definition A.1', 'Algorithm S1').replace('def:third', 'supp:alg:first'))
        self.article.write_text(self.article.read_text().replace(
            'Definition A.1', 'Algorithm S1').replace('def:third', 'supp:alg:first'))
        self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def test_short_numbers_are_reserved_for_algorithms(self):
        self.table.write_text(self.table.read_text().replace('Definition A.1', 'Theorem S1'))
        with self.assertRaisesRegex(ValueError, 'Invalid mathematical claim number'):
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

    def test_known_gap_allows_proof_checks_without_claiming_complete_coverage(self):
        self.table.write_text(self.table.read_text() + '\n<!-- article-unresolved: thm:first -->\n')
        output = io.StringIO()
        with redirect_stdout(output):
            result = ArticleCoverage.check(self.project)
        self.assertFalse(result['complete'])
        self.assertEqual(result['numbered_claims'], 3)
        self.assertEqual(result['verified_numbered_claims'], 0)
        self.assertEqual(result['unresolved_obligations'], ['thm:first'])
        self.assertIn('INCOMPLETE', output.getvalue())

    def test_incomplete_review_still_rejects_signature_mismatch(self):
        self.table.write_text(self.table.read_text() + '\n<!-- article-unresolved: thm:first -->\n')
        self.article.write_text(self.article.read_text().replace('@Example.first', '@Example.other'))
        with self.assertRaisesRegex(ValueError, 'ordered showcase'):
            ArticleCoverage.check(self.project)

if __name__ == '__main__':
    unittest.main()

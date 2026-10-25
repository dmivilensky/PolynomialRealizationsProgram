"""Reject stale, incomplete or misleading article-coverage records."""
from contextlib import redirect_stdout
import hashlib
import io
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest

from Tools.Verification import ArticleCoverage


class ArticleMapReviewTests(unittest.TestCase):
    """Check the numbered and unnumbered inventory against its reviewed source."""

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.directory = self.root / 'Example'
        self.directory.mkdir()
        self.source = self.root / 'paper.tex'
        self.source.write_text(r'''\section{Results}
\begin{theorem}[First]\label{thm:first}A.\end{theorem}
\begin{remark}A numbered remark.\end{remark}
\begin{lemma}\label{lem:second}B.\end{lemma}
\appendix
\section{Proofs}
\begin{definition}[Third]\label{def:third}C.\end{definition}''')
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
        self.table.write_text(f'''# Correspondence
<!-- article-source: paper.tex sha256={hashlib.sha256(self.source.read_bytes()).hexdigest()} -->
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

    def test_map_alone_guards_all_numbered_and_unnumbered_mathematics(self):
        self.assertEqual(self.check()['verified_numbered_claims'], 3)

    def test_shared_counter_and_appendix_numbers_are_read_from_article(self):
        self.assertEqual([item['number'] for item in ArticleCoverage.ordered_claims(
            self.source.read_text())], ['1.1', '1.3', 'A.1'])

    def test_changed_statement_invalidates_the_semantic_review(self):
        self.source.write_text(self.source.read_text().replace('A.', 'Stronger A.'))
        with self.assertRaisesRegex(ValueError, 'Stale'):
            self.check()

    def test_missing_reordered_or_relabelled_result_is_rejected(self):
        original = self.table.read_text()
        for changed in [original.replace('1.3', '1.2'),
                        original.replace('lem:second', 'lem:other'),
                        original.replace(' — First', ''),
                        '\n'.join(line for line in original.splitlines() if '| Lemma' not in line)]:
            with self.subTest(changed=changed):
                self.table.write_text(changed)
                with self.assertRaisesRegex(ValueError, 'inventory differs'):
                    self.check()

    def test_showcase_cannot_reference_different_declarations(self):
        self.article.write_text(self.article.read_text().replace('@Example.second', '@Example.other'))
        with self.assertRaisesRegex(ValueError, 'ordered showcase'):
            self.check()

    def test_showcase_numbers_and_labels_must_match_pdf_order(self):
        self.article.write_text(self.article.read_text().replace('Lemma 1.3', 'Lemma 1.2'))
        with self.assertRaisesRegex(ValueError, 'Showcase comments differ'):
            self.check()

    def test_showcase_title_must_match_the_article(self):
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

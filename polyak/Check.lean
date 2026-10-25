import polyak.Article
import Verification.Audit

/-!
Article: Two Answers on Heavy-Ball Dynamics — complete package verification.
Use: check source coverage and the transitive axioms of every owned declaration,
including private and generated declarations, using the shared project audit.
Run `python3 -m Tools.Verification.Check polyak` from the workspace root.
Article.lean follows all numbered results in PDF order; ArticleMap.md records
their precise mathematical correspondence and the additional unnumbered results.
-/

run_cmd Verification.audit `polyak "polyak"

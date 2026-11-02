import krylov.Article
import Verification.Audit

/-!
Article: Adaptive Krylov Methods under Hessian Variation — complete package audit.
Use: verify every krylov source and every module-owned declaration, including
private/generated names, with the existing independent transitive-axiom checks.
Article.lean follows the current numbered results in PDF order;
ArticleMap.md records their hypotheses and the additional unnumbered mathematics.
Run `python3 -m Tools.Verification.Check krylov --require-complete` from the
workspace root to require both the reviewed source coverage and this axiom audit.
-/

set_option maxHeartbeats 0 in
run_cmd Verification.audit `krylov "krylov"

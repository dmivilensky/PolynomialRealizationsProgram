import jacobi.Article
import Verification.Audit

/-!
Article: jacobi — complete verification entry point for the mathematical package.
Use: Article checks the ordered source references. The audit requires every
owned source to be imported, then inspects every owned declaration and all
transitive axiom dependencies using two independent collection methods.
ArticleMap.md states auxiliary proof replacements and the excluded decimal
illustrations. Run python3 -m Tools.Verification.Check jacobi.
-/

set_option maxHeartbeats 0 in
run_cmd Verification.audit `jacobi "jacobi"

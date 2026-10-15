import «2606.16671v2».Article
import PolynomialRealizationsProgram.Audit

/-!
Article: 2606.16671v2 — complete verification entry point.
Use: `Article` imports the entire mathematical library and checks the article statements in order.
`PolynomialRealizationsProgram.audit` checks every source is imported, every module-owned
public/private/generated declaration, and all axiom dependencies by two collection methods.
Run `python3 Scripts/Check.py 2606.16671v2` from the project root.
-/

set_option maxHeartbeats 0 in
run_cmd PolynomialRealizationsProgram.audit `«2606.16671v2» "2606.16671v2"

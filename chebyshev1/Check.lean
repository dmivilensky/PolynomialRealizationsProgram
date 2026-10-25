import chebyshev1.Article
import Verification.Audit

/-!
Article: chebyshev1 — complete verification entry point.
Use: `Article` imports the entire mathematical library and checks the article statements in order.
`Verification.audit` checks every source is imported, every module-owned
public/private/generated declaration, and all axiom dependencies by two collection methods.
Run `python3 -m Tools.Verification.Check chebyshev1` from the project root.
-/

set_option maxHeartbeats 0 in
run_cmd Verification.audit `chebyshev1 "chebyshev1" #[`chebyshev1.Numerics.EnergyWitnessGenerator]

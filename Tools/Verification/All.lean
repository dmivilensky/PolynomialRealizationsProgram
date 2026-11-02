import bezout.Check
import chebyshev1.Check
import chebyshev2.Check
import jacobi.Check
import krylov.Check
import polyak.Check

/-!
Shared complete-check entry point, maintained by `python3 -m Tools.Verification.Check all`.
Use: import every discovered package Check, including its source and axiom audits.
The checked mathematical coverage is documented in each package's own showcase and table.
-/

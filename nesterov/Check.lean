import nesterov.Article
import Verification.Audit

/-!
Complete source and transitive-axiom audit for the implemented Nesterov library.
Mathematical article coverage is tracked separately in ArticleMap.md.
Only propext, Classical.choice and Quot.sound are permitted; private and generated
declarations are audited together with public theorems.
-/
set_option maxHeartbeats 0 in
run_cmd Verification.audit `nesterov "nesterov"

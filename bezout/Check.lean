import bezout.Article
import Verification.Audit

/-!
Article: bezout, complete verification of the mathematical package.
Use: the ordered showcase and correspondence describe the proved mathematical scope;
the audit includes all owned public, private and generated declarations and
requires every package source to occur in the import closure.
Proof trust: only propext, Classical.choice and Quot.sound are permitted as
transitive axioms. No unsafe proposal helper or additional exception is used.
-/

set_option maxHeartbeats 0 in
run_cmd Verification.audit `bezout "bezout"

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine consecutive virtual injections.
Use: recover every true accumulated effective-gradient injection from its actual chronological differences, including the empty initial prefix.
Source: exact finite telescoping of the real accumulated injection sequence.
-/

namespace krylov.Envelope
open scoped BigOperators
variable {E : Type*} [AddCommGroup E]

/-- The genuine successive injection of an actual accumulated physical defect sequence.
Use: The genuine successive injection of an actual accumulated physical defect sequence.
Article: main_krylov, thm:E1, genuine consecutive virtual injections.
Proof: Subtract the two actual consecutive accumulated defects and set the empty injection to zero. -/
def injectionDifference (J : ℕ → E) : ℕ → E
  | 0 => 0
  | k+1 => J (k+1)-J k

/-- The actual finite sum of genuine consecutive injections recovers the original accumulated defect with zero initial value.
Use: The actual finite sum of genuine consecutive injections recovers the original accumulated defect with zero initial value.
Article: main_krylov, thm:E1, genuine consecutive virtual injections.
Proof: Telescope the actual finite chronological differences. -/
theorem injectionDifference_sum (J : ℕ → E) (h0 : J 0=0) (k : ℕ) :
    ∑ i∈Finset.range k,injectionDifference J (i+1)=J k := by
  induction k with
  | zero => simpa only [Finset.sum_range_zero] using h0.symm
  | succ k ih => rw [Finset.sum_range_succ,ih,injectionDifference];abel
end krylov.Envelope

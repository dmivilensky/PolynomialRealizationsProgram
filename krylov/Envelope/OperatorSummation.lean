import Mathlib.Algebra.BigOperators.Intervals
import krylov.Envelope.FirstJets
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine physical operator summation by parts.
Use: convert actual output-minus-segment and cumulative source-defect actions into original chronological weighted-step prefix sums.
Source: exact finite chronological telescoping and linearity of the true physical operator actions.
-/

namespace krylov.Envelope
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual sum of physical operator tails acting on original vectors equals the genuine increment action on their chronological partial sums.
Use: The actual sum of physical operator tails acting on original vectors equals the genuine increment action on their chronological partial sums.
Article: main_krylov, thm:E1, genuine physical operator summation by parts.
Proof: Append the real final operator increment and combine all its true physical actions by linearity. -/
theorem operator_tail_prefix_sum (D : ℕ → E →ₗ[ℝ] E) (v : ℕ → E) (N : ℕ) :
    (∑ i∈Finset.range N,(∑ l∈Finset.Ico i N,D l) (v i))=
      ∑ l∈Finset.range N,D l (∑ i∈Finset.range (l+1),v i) := by
  -- Append the actual final physical increment before collecting its genuine earlier chronological vector actions.
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    have hsplit : (∑ i∈Finset.range N,(∑ l∈Finset.Ico i (N+1),D l) (v i))=
        (∑ i∈Finset.range N,(∑ l∈Finset.Ico i N,D l) (v i))+∑ i∈Finset.range N,D N (v i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_Ico_succ_top (Finset.mem_range.mp hi).le D,LinearMap.add_apply]
    rw [hsplit,ih,← map_sum,Finset.sum_range_succ,map_add]
    simp only [Nat.Ico_succ_singleton,Finset.sum_singleton]
    abel

/-- Zero total genuine physical displacement converts actual cumulative increment actions into the negative true increment actions on chronological prefixes.
Use: Zero total genuine physical displacement converts actual cumulative increment actions into the negative true increment actions on chronological prefixes.
Article: main_krylov, thm:E1, genuine physical operator summation by parts.
Proof: Subtract the actual tail-prefix identity from the real constant-total operator action, whose genuine vector sum vanishes. -/
theorem operator_cumulative_by_parts (D : ℕ → E →ₗ[ℝ] E) (v : ℕ → E) (N : ℕ)
    (hzero : ∑ i∈Finset.range N,v i=0) :
    (∑ i∈Finset.range N,(∑ l∈Finset.range i,D l) (v i))=
      -(∑ l∈Finset.range N,D l (∑ i∈Finset.range (l+1),v i)) := by
  -- A genuine zero total displacement cancels the actual full cumulative operator action.
  have h := operator_tail_prefix_sum D v N
  have ht : (∑ i∈Finset.range N,(∑ l∈Finset.Ico i N,D l) (v i))=
      -(∑ i∈Finset.range N,(∑ l∈Finset.range i,D l) (v i)) := by
    have he (i : ℕ) (hi : i<N) : (∑ l∈Finset.Ico i N,D l)=
        (∑ l∈Finset.range N,D l)-(∑ l∈Finset.range i,D l) :=
      Finset.sum_Ico_eq_sub D hi.le
    simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun T : E →ₗ[ℝ] E => T (v i)) (he i (Finset.mem_range.mp hi)))]
    simp only [LinearMap.sub_apply,Finset.sum_sub_distrib,← map_sum,hzero,map_zero,zero_sub]
  rw [ht] at h
  exact neg_eq_iff_eq_neg.mp h
end krylov.Envelope

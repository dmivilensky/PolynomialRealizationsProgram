import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Split the literal finite spectrum into a right half and a reversed left
half, assigning a possible middle node only to the right. This identity
is used for the full original gap-logarithm product limit.
Use: gapProduct_log_tendsto applies dominated convergence to the two actual original spectral half-rows without duplicating or omitting a middle node.
-/
namespace jacobi.Finite
open Finset

/-- A complete finite row is the sum of its right half and its strictly reflected left half.
Use: gapProduct_log_tendsto applies dominated convergence to the two actual original spectral half-rows without duplicating or omitting a middle node.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Source: finite-sum reflection and the partition of an integer interval into its two halves.
Proof: reverse the strict reflected half-sum. Its reflected inequality is exactly the complement of the first half-inequality. At every original index the two indicator terms then add to the original summand. -/
theorem sum_two_halves (n:ℕ) (f:ℕ→ℝ) :
    (∑j∈range (n+1),f j)=(∑j∈range (n+1),if 2*j≤n then f j else 0)+
      ∑j∈range (n+1),if 2*j<n then f (n-j) else 0 := by
  -- The strict reflected half is necessary at even last index, where one actual middle node occurs.
  have he : (∑j∈range (n+1),if 2*j<n then f (n-j) else 0)=
      ∑j∈range (n+1),if 2*j≤n then 0 else f j := by
    rw [← sum_range_reflect (fun j => if 2*j<n then f (n-j) else 0) (n+1)]
    apply sum_congr rfl
    intro j hj
    have hjn : j≤n := by have := mem_range.mp hj; omega
    have h₁ : n+1-1-j=n-j := by omega
    have h₂ : n-(n-j)=j := by omega
    rw [h₁,h₂]
    by_cases h:2*j≤n
    · rw [ite_eq_right (show ¬2*(n-j)<n by omega),ite_eq_left h]
    · rw [ite_eq_left (show 2*(n-j)<n by omega),ite_eq_right h]
  rw [he,← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h:2*j≤n <;> simp only [h,ite_true,ite_false,add_zero,zero_add]

end jacobi.Finite

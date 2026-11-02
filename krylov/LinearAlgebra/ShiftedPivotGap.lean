import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), actual original-to-shifted Jacobi pivot gap.
Use: convert genuine positive shifted pivots into a true lower barrier for the original actual pivots.
Source: both original scalar LDL recurrences and actual positive reciprocal-order comparison.
-/

namespace krylov.LinearAlgebra
noncomputable section

/-- The actual original positive Jacobi pivots stay at least the genuine positive shift above their true shifted companions.
Use: The actual original positive Jacobi pivots stay at least the genuine positive shift above their true shifted companions.
Article: main_krylov, prop:phi(c), actual original-to-shifted Jacobi pivot gap.
Proof: Induct through both actual Riccati updates and use the genuine shifted-pivot reciprocal inequality. -/
theorem positive_shifted_pivot_gap (d s A B : ℕ → ℝ) (mu : ℝ) (hmu : 0≤mu)
    (hs : ∀ n,0 < s n) (hzero : d 0=mu+s 0)
    (hdrec : ∀ n,d (n+1)=A (n+1)-(B n)^2/d n)
    (hsrec : ∀ n,s (n+1)=A (n+1)-mu-(B n)^2/s n) :
    ∀ n,mu+s n≤d n := by
  -- The actual preceding shift gap fixes the genuine reciprocal order before the next true pivot update.
  intro n
  induction n with
  | zero => exact hzero.ge
  | succ n ih =>
    have hsd : s n≤d n := by linarith
    have hi : (d n)⁻¹≤(s n)⁻¹ := inv_anti₀ (hs n) hsd
    have hm := mul_le_mul_of_nonneg_left hi (sq_nonneg (B n))
    rw [hdrec,hsrec]
    simp only [← div_eq_mul_inv] at hm
    linarith
end
end krylov.LinearAlgebra

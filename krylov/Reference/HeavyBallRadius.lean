import krylov.Reference.HeavyBallMatrix
import krylov.LinearAlgebra.GershgorinInterval
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), actual heavy-ball Gershgorin radii.
Use: prove the genuine physical heavy-ball spectral window from the original finite matrix entries, preserving its special first diagonal boundary.
Source: actual adjacent-site sparsity and the proved genuine one-site finite sum bound.
-/

namespace krylov.Reference
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped BigOperators
variable {N : ℕ}

/-- The genuine physical heavy-ball off-diagonal row radius is at most one coupling plus its actual present predecessor coupling.
Use: The genuine physical heavy-ball off-diagonal row radius is at most one coupling plus its actual present predecessor coupling.
Article: main_krylov, prop:phi(b), actual heavy-ball Gershgorin radii.
Proof: Only the true adjacent sites contribute; each original finite site contributes at most its genuine positive coupling magnitude. -/
theorem heavyBall_row_radius (d q : ℝ) (hd : 0 < d) (hq : 0 < q) (i : Fin N) :
    (∑ j∈Finset.univ.erase i,‖heavyBallMatrix d q N i j‖)≤
      d*q+(if 0 < i.val then d*q else 0) := by
  -- Count the genuine successor and predecessor sites separately so the actual first-row boundary is retained.
  let b := d*q
  have hb : 0≤b := (mul_pos hd hq).le
  let f : Fin N → ℝ := fun j =>
    (if j.val=i.val+1 then b else 0)+(if j.val+1=i.val then b else 0)
  have hentry (j : Fin N) (hj : j∈Finset.univ.erase i) :
      ‖heavyBallMatrix d q N i j‖≤f j := by
    have hji : j≠i := (Finset.mem_erase.mp hj).1
    rw [heavyBallMatrix,ite_eq_right hji.symm]
    dsimp only [f,b]
    by_cases h1 : i.val+1=j.val
    · have h2 : ¬ j.val+1=i.val := by omega
      simp [h1,h2,Real.norm_eq_abs,abs_of_pos hd,abs_of_pos hq]
    · by_cases h2 : j.val+1=i.val
      · simp [h1,h2,show j.val≠i.val+1 by omega,Real.norm_eq_abs,abs_of_pos hd,abs_of_pos hq]
      · simp [h1,h2,show j.val≠i.val+1 by omega]
  -- Extend only nonnegative actual site budgets before applying the genuine finite-site bounds.
  calc
    _ ≤ ∑ j∈Finset.univ.erase i,f j := Finset.sum_le_sum hentry
    _ ≤ ∑ j : Fin N,f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _)
      (fun j _ _ => add_nonneg (by split <;> positivity) (by split <;> positivity))
    _ = (∑ j : Fin N,if j.val=i.val+1 then b else 0)+
        (∑ j : Fin N,if j.val+1=i.val then b else 0) := Finset.sum_add_distrib
    _ ≤ b+(if 0 < i.val then b else 0) := by
      apply add_le_add (finite_site_sum_le N (i.val+1) b hb)
      by_cases hi : 0 < i.val
      · rw [ite_eq_left hi]
        have he (j : Fin N) : j.val+1=i.val ↔ j.val=i.val-1 := by omega
        simp only [he]
        exact finite_site_sum_le N (i.val-1) b hb
      · simp [hi,show ∀ j : Fin N,j.val+1≠i.val by intro j;omega]
end
end krylov.Reference

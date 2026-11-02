import krylov.LinearAlgebra.SchurProduct
import Mathlib.LinearAlgebra.Matrix.Gershgorin
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), actual heavy-ball spectral enclosure.
Use: turn genuine physical row bounds into actual finite Hermitian eigenvalue intervals.
Source: mathlib Gershgorin eigenvalue closed-ball theorem and elementary actual finite-site counting.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every actual real Hermitian eigenvalue lies in the genuine interval certified by its physical Gershgorin rows.
Use: Every actual real Hermitian eigenvalue lies in the genuine interval certified by its physical Gershgorin rows.
Article: main_krylov, prop:phi(b), actual heavy-ball spectral enclosure.
Proof: Apply the standard true eigenvalue disk theorem and combine the actual lower and upper row inequalities. -/
theorem eigenvalues_interval_of_rows (T : Matrix ι ι ℝ) (hT : T.IsHermitian)
    (a b : ℝ) (hlo : ∀ k,a+(∑ j∈Finset.univ.erase k,‖T k j‖)≤T k k)
    (hhi : ∀ k,T k k+(∑ j∈Finset.univ.erase k,‖T k j‖)≤b) :
    ∀ i,a≤hT.eigenvalues i ∧ hT.eigenvalues i≤b := by
  -- Use the actual matrix eigenvalue in the genuine row-disk theorem before comparing either spectral endpoint.
  intro i
  have he : Module.End.HasEigenvalue (Matrix.toLin' T) (hT.eigenvalues i) :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr (by
      rw [Matrix.spectrum_toLin']
      exact hT.eigenvalues_mem_spectrum_real i)
  obtain ⟨k,hk⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall,Real.dist_eq] at hk
  have hb := abs_le.mp hk
  exact ⟨by linarith [hlo k,hb.1],by linarith [hhi k,hb.2]⟩

/-- A genuine finite coordinate site contributes at most its nonnegative budget.
Use: A genuine finite coordinate site contributes at most its nonnegative budget.
Article: main_krylov, prop:phi(b), actual heavy-ball spectral enclosure.
Proof: At a real present index the sum has exactly one term; outside the actual dimension it vanishes. -/
theorem finite_site_sum_le (N r : ℕ) (b : ℝ) (hb : 0≤b) :
    (∑ j : Fin N,if j.val=r then b else 0)≤b := by
  by_cases hr : r<N
  · have he (j : Fin N) : j.val=r ↔ j=(⟨r,hr⟩ : Fin N) := by simp only [Fin.ext_iff]
    simp only [he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,le_refl]
  · have he (j : Fin N) : j.val≠r := by omega
    simpa only [he,ite_false,Finset.sum_const_zero] using hb
end
end krylov.LinearAlgebra

import nesterov.Faithful.FamilyPolynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Coefficient regularity of the exact ξ-polynomial. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology BigOperators
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem familyA_coeff_ck {k : ℕ} (hk : F.CoeffCk k) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(familyA F ε).coeff j) (Ici 0) 0 := by
  unfold familyA
  simp_rw [Polynomial.coeff_mul]
  apply ContDiffWithinAt.sum
  intro ab _
  apply contDiffWithinAt_const.mul
  simp only [coeff_sub]
  have hmul : ContDiffWithinAt ℝ k (fun ε=>(C (ε^2)*F.u ε).coeff ab.2) (Ici 0) 0 := by
    simp only [coeff_C_mul]
    exact (contDiffWithinAt_id.pow 2).mul (hk.1 ab.2)
  exact hmul.sub (hk.2 ab.2)

theorem familyB_coeff_ck {k : ℕ} (hk : F.CoeffCk k) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(familyB F ε).coeff j) (Ici 0) 0 := by
  simpa only [familyB,coeff_sub] using (hk.1 j).sub (hk.2 j)

theorem circleProductPolynomial_coeff_ck {A B : ℝ→Polynomial ℝ} {r : ℝ→ℝ} {k : ℕ}
    (hA : ∀ j,ContDiffWithinAt ℝ k (fun ε=>(A ε).coeff j) (Ici 0) 0)
    (hB : ∀ j,ContDiffWithinAt ℝ k (fun ε=>(B ε).coeff j) (Ici 0) 0)
    (hr : ContDiffWithinAt ℝ k r (Ici 0) 0) (N j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(circleProductPolynomial N (A ε) (B ε) (r ε)).coeff j) (Ici 0) 0 := by
  simp only [circleProductPolynomial,finsetSum_coeff,coeff_C_mul]
  apply ContDiffWithinAt.sum
  intro a _
  apply ContDiffWithinAt.sum
  intro b _
  exact (((hA a).mul (hB b)).mul (hr.pow (a+b))).mul contDiffWithinAt_const

theorem familyPolynomial_coeff_ck {k : ℕ} (hk : F.CoeffCk k) (c : ℝ) (j : ℕ) :
    ContDiffWithinAt ℝ k (fun ε=>(familyPolynomial F c ε).coeff j) (Ici 0) 0 := by
  apply circleProductPolynomial_coeff_ck (familyA_coeff_ck F hk) (familyB_coeff_ck F hk)
  exact (contDiffWithinAt_const.mul contDiffWithinAt_id).exp

end
end nesterov.Faithful

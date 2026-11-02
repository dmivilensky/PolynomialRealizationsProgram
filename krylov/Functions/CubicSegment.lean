import krylov.Functions.HiddenCubic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
Article: main_krylov, thm:Fexact, exact function-value information on cubic functions.
Use: work with a genuine continuous symmetric trilinear form and a differentiated
scalar potential; derive the trapezoid defect without assuming its expansion.
Source: exact cubic Taylor algebra in Appendix G of main_krylov.
-/

namespace krylov.Functions
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous symmetric trilinear form, represented by curried continuous linear maps.
Article: main_krylov, thm:Htransfer and thm:Fexact.
Use: the symmetry fields specify tensor symmetry, not any desired numerical estimate. -/
structure SymmetricCubic (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  form : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ
  swap₁ : ∀ a b c, form a b c = form b a c
  swap₂ : ∀ a b c, form a b c = form a c b

namespace SymmetricCubic

/-- The scalar cubic potential whose third derivative is the given form.
Article: main_krylov, thm:Fexact. -/
def potential (T : SymmetricCubic E) (x : E) : ℝ := T.form x x x / 6

/-- Exact differential of the cubic potential.
Article: main_krylov, thm:Fexact.
Proof: differentiate all three slots, then use tensor symmetry. -/
theorem potential_hasFDerivAt (T : SymmetricCubic E) (x : E) :
    HasFDerivAt T.potential ((1 / 2 : ℝ) • T.form x x) x := by
  have h := ((T.form.hasFDerivAt.clm_apply (hasFDerivAt_id x)).clm_apply
    (hasFDerivAt_id x)).mul_const (1 / 6 : ℝ)
  convert! h using 1
  · ext y
    simp only [potential, div_eq_mul_inv, id_eq, one_mul]
  · ext v
    simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
    rw [T.swap₁ v x x, T.swap₂ x v x]
    ring

/-- Trilinearity gives the exact cubic Taylor formula, with no asymptotic premise.
Article: main_krylov, thm:Fexact. -/
theorem potential_add (T : SymmetricCubic E) (a s : E) :
    T.potential (a + s) = T.potential a + T.form a a s / 2 +
      T.form a s s / 2 + T.form s s s / 6 := by
  simp only [potential, map_add, add_apply]
  simp only [T.swap₂ a s a, T.swap₁ s a a, T.swap₁ s a s, T.swap₂ s s a]
  ring

/-- The exact trapezoid defect of a cubic along an arbitrary segment.
Article: main_krylov, thm:Fexact, delta_tr = -T(s,s,s)/12.
Proof: subtract the endpoint differentials from the exact cubic value increment. -/
theorem trapezoid_defect (T : SymmetricCubic E) (a s : E) :
    T.potential (a + s) - T.potential a -
      (T.form a a s / 2 + T.form (a + s) (a + s) s / 2) / 2 =
      -T.form s s s / 12 := by
  rw [T.potential_add]
  simp only [map_add, add_apply]
  rw [T.swap₁ s a s]
  ring

/-- The cubic secant diagonal is the Hessian diagonal at the segment midpoint.
Article: main_krylov, thm:Fexact.
Proof: average the two quadratic directional derivatives and expand the midpoint. -/
theorem midpoint_diagonal (T : SymmetricCubic E) (a s : E) :
    T.form (a + s) (a + s) s / 2 - T.form a a s / 2 =
      T.form (a + (1 / 2 : ℝ) • s) s s := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [T.swap₁ s a s]
  ring

/-- Function values correct the diagonal exactly at every anchor on the segment line.
Article: main_krylov, thm:Fexact.
Proof: combine the midpoint diagonal and exact cubic trapezoid defect. -/
theorem corrected_diagonal (T : SymmetricCubic E) (a s : E) (l : ℝ) :
    T.form (a + (1 / 2 : ℝ) • s) s s -
      12 * l * (-T.form s s s / 12) =
      T.form (a + (1 / 2 : ℝ) • s + l • s) s s := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

end SymmetricCubic
end
end krylov.Functions

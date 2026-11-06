import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The radial norm derivative associated with a second-order vector expansion.
Both the nonzero leading term and the degenerate leading term are covered.
-/
namespace chebyshev1.Perturbations
noncomputable section
open Filter Asymptotics
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The continuous-at-zero normalization of an error trajectory along one ray. -/
def radialVector (e : ℝ → E) (a : E) (r : ℝ) : E :=
  if r = 0 then a else r⁻¹ • e r

@[simp] theorem radialVector_zero (e : ℝ → E) (a : E) : radialVector e a 0 = a := by
  simp [radialVector]

/-- Dividing a second-order expansion by its radius leaves derivative `b`. -/
theorem radialVector_hasDerivAt (e : ℝ → E) (a b : E)
    (hexp : (fun r => e r - (r • a + r ^ 2 • b)) =o[𝓝 0] (fun r : ℝ => r ^ 2)) :
    HasDerivAt (radialVector e a) b 0 := by
  have h := (isBigO_refl (fun r : ℝ => r⁻¹) (𝓝 0)).smul_isLittleO hexp
  apply HasDerivAt.of_isLittleO
  convert h using 1
  · funext r
    by_cases hr : r = 0
    · simp [hr, radialVector]
    · simp [radialVector, hr, smul_sub, smul_add, smul_smul, pow_two]
      abel
  · funext r
    by_cases hr : r = 0
    · simp [hr]
    · simp [smul_eq_mul, pow_two, ← mul_assoc, inv_mul_cancel₀ hr]

/-- The derivative of the norm at a nonzero leading vector. -/
theorem norm_hasDerivAt_of_ne_zero {q : ℝ → E} {a b : E}
    (hq : HasDerivAt q b 0) (hqa : q 0 = a) (ha : a ≠ 0) :
    HasDerivAt (fun r => ‖q r‖) (⟪a, b⟫ / ‖a‖) 0 := by
  have h := hq.norm_sq.sqrt (by simp [hqa, ha])
  convert h using 1
  · funext r
    simp
  · simp [hqa, mul_div_mul_left]

/-- When the leading vector vanishes, the right derivative is the norm of `b`. -/
theorem norm_hasDerivWithinAt_of_zero {q : ℝ → E} {b : E}
    (hq : HasDerivAt q b 0) (hq0 : q 0 = 0) :
    HasDerivWithinAt (fun r => ‖q r‖) ‖b‖ (Set.Ioi 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  have h := hq.tendsto_slope_zero_right.norm
  simp only [zero_add, hq0, sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  simp [slope, hq0, norm_smul, Real.norm_eq_abs, smul_eq_mul, hrpos.le]

/-- The two cases in the right derivative of a norm. -/
def radialSlope (a b : E) : ℝ := by
  classical
  exact if a = 0 then ‖b‖ else ⟪a, b⟫ / ‖a‖

/-- Complete right-derivative formula for the normalized terminal error. -/
theorem radialNorm_hasDerivWithinAt (e : ℝ → E) (a b : E)
    (hexp : (fun r => e r - (r • a + r ^ 2 • b)) =o[𝓝 0] (fun r : ℝ => r ^ 2)) :
    HasDerivWithinAt (fun r => ‖radialVector e a r‖)
      (radialSlope a b) (Set.Ioi 0) 0 := by
  have h := radialVector_hasDerivAt e a b hexp
  by_cases ha : a = 0
  · subst a
    simp only [radialSlope, ite_true]
    exact norm_hasDerivWithinAt_of_zero h (by simp)
  · simp only [radialSlope, ha, ite_false]
    exact (norm_hasDerivAt_of_ne_zero h (by simp) ha).hasDerivWithinAt

/-- Linear leading terms are odd and quadratic corrections are even on opposite rays. -/
theorem opposite_radial_slopes (a b : E) :
    ⟪-a, b⟫ / ‖-a‖ = -(⟪a, b⟫ / ‖a‖) := by
  simp [neg_div]

end
end chebyshev1.Perturbations

import krylov.XR.AlgorithmState

/-!
Article: main_krylov, alg:xr, safeguard (G).
Use: derive the two gradient-related inequalities from the actual clipped
fallback, without assuming them as fields of a model-step oracle.
Source: elementary reciprocal order and the Hilbert-space norm identities.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Literal clipping interval for the fallback curvature. -/
def clippedCurvature (c₁ c₂ rho : ℝ) : ℝ :=
  max c₂⁻¹ (min c₁⁻¹ rho)

/-- The two inequalities tested by safeguard (G). -/
def GradientRelated (c₁ c₂ : ℝ) (g u : E) : Prop :=
  inner ℝ g u ≤ -c₁ * ‖g‖ ^ 2 ∧ ‖u‖ ≤ c₂ * ‖g‖

/-- Actual safeguard: retain a passing model step, otherwise take the
negative gradient with the printed clipped scalar curvature. -/
def safeguard (c₁ c₂ rho : ℝ) (g u : E) : E := by
  classical
  exact if GradientRelated c₁ c₂ g u then u
    else -(clippedCurvature c₁ c₂ rho)⁻¹ • g

/-- A positive ordered safeguard interval clips every real input to it. -/
theorem clippedCurvature_bounds (c₁ c₂ rho : ℝ) (h₁ : 0 < c₁)
    (h₂ : c₁ ≤ c₂) :
    0 < clippedCurvature c₁ c₂ rho ∧
      c₂⁻¹ ≤ clippedCurvature c₁ c₂ rho ∧
      clippedCurvature c₁ c₂ rho ≤ c₁⁻¹ := by
  have hc₂ : 0 < c₂ := h₁.trans_le h₂
  have hi : c₂⁻¹ ≤ c₁⁻¹ := inv_le_inv₀ hc₂ h₁ |>.2 h₂
  refine ⟨(inv_pos.mpr hc₂).trans_le (le_max_left _ _), le_max_left _ _, ?_⟩
  exact max_le hi (min_le_left _ _)

/-- The literal fallback has both required gradient-related bounds. -/
theorem fallback_gradientRelated (c₁ c₂ rho : ℝ) (h₁ : 0 < c₁)
    (h₂ : c₁ ≤ c₂) (g : E) :
    GradientRelated c₁ c₂ g (-(clippedCurvature c₁ c₂ rho)⁻¹ • g) := by
  have hc := clippedCurvature_bounds c₁ c₂ rho h₁ h₂
  have hc₂ : 0 < c₂ := h₁.trans_le h₂
  have hlo : c₁ ≤ (clippedCurvature c₁ c₂ rho)⁻¹ := by
    have h := (inv_le_inv₀ (inv_pos.mpr h₁) hc.1).2 hc.2.2
    simpa using h
  have hhi : (clippedCurvature c₁ c₂ rho)⁻¹ ≤ c₂ := by
    have h := (inv_le_inv₀ hc.1 (inv_pos.mpr hc₂)).2 hc.2.1
    simpa using h
  constructor
  · simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id,
      id_eq]
    nlinarith [sq_nonneg ‖g‖]
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hc.1)]
    exact mul_le_mul_of_nonneg_right hhi (norm_nonneg g)

/-- Every actual safeguarded output satisfies (G), independently of the
model, the data, the trial curvature, and whether the fallback was used. -/
theorem safeguard_gradientRelated (c₁ c₂ rho : ℝ) (h₁ : 0 < c₁)
    (h₂ : c₁ ≤ c₂) (g u : E) :
    GradientRelated c₁ c₂ g (safeguard c₁ c₂ rho g u) := by
  unfold safeguard
  split
  · assumption
  · exact fallback_gradientRelated c₁ c₂ rho h₁ h₂ g

/-- At a nonstationary point the safeguarded direction has strictly
negative slope, so every tested positive step has a positive denominator. -/
theorem safeguard_slope_neg (c₁ c₂ rho : ℝ) (h₁ : 0 < c₁)
    (h₂ : c₁ ≤ c₂) (g u : E) (hg : g ≠ 0) :
    inner ℝ g (safeguard c₁ c₂ rho g u) < 0 := by
  have h := (safeguard_gradientRelated c₁ c₂ rho h₁ h₂ g u).1
  have hn : 0 < ‖g‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  exact h.trans_lt (by nlinarith)

/-- A model step satisfying the actual tests is retained exactly. -/
theorem safeguard_eq_of_gradientRelated (c₁ c₂ rho : ℝ) (g u : E)
    (h : GradientRelated c₁ c₂ g u) : safeguard c₁ c₂ rho g u = u := by
  classical
  simp only [safeguard, ite_eq_left h]

/-- Stronger primitive local step bounds imply that safeguard (G) is
inactive, for every fallback curvature and even at a zero gradient. -/
theorem safeguard_eq_of_stronger_bounds (c₁ c₂ cflat Cflat rho : ℝ) (g u : E)
    (h : GradientRelated cflat Cflat g u) (hc₁ : c₁ ≤ cflat) (hc₂ : Cflat ≤ c₂) :
    safeguard c₁ c₂ rho g u = u := by
  apply safeguard_eq_of_gradientRelated
  constructor
  · nlinarith [h.1, mul_le_mul_of_nonneg_right hc₁ (sq_nonneg ‖g‖)]
  · exact h.2.trans (mul_le_mul_of_nonneg_right hc₂ (norm_nonneg g))

end
end krylov.XR

import krylov.Functions.QuadraticHiddenFamily
import krylov.Tensor.CubicBanach

/-!
Article: main_krylov, apA:lem:angle, actual rank-one tensor geometry.
Use: compute the true attained cubic diagonal norm, the exact hidden-family
midpoint drift and its normalized cosine. The undivided identity includes
zero tensors and zero midpoint displacements; the divided angle identity
explicitly requires its nonzero denominator.
Source: the rank-one family in Appendix G and Hilbert-space Cauchy--Schwarz.
-/

namespace krylov.Functions
noncomputable section
open Set InnerProductSpace chebyshev1.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine symmetric rank-one cubic tensor c times the cube of an inner coordinate.
Article: main_krylov, apA:lem:angle. -/
def rankOneCubic (a : E) (c : ℝ) : SymmetricCubic E where
  form := (c • innerSL ℝ a).smulRight (coordinateSquare (innerSL ℝ a))
  swap₁ := by
    intro u v w
    simp only [coordinateSquare, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  swap₂ := by
    intro u v w
    simp only [coordinateSquare, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring

/-- The actual rank-one trilinear evaluation is the product of its three coordinates.
Article: main_krylov, apA:lem:angle. Proof: evaluate the continuous multilinear construction. -/
theorem rankOneCubic_apply (a : E) (c : ℝ) (u v w : E) :
    (rankOneCubic a c).form u v w = c * inner ℝ a u * inner ℝ a v * inner ℝ a w := by
  simp [rankOneCubic, coordinateSquare]
  ring

/-- The actual rank-one cubic has its printed unit-diagonal upper bound.
Article: main_krylov, apA:lem:angle. Proof: apply genuine Cauchy--Schwarz to the coordinate. -/
theorem rankOneCubic_diagonal_bound (a : E) (c : ℝ) (u : E) (hu : ‖u‖ = 1) :
    |(rankOneCubic a c).form u u u| ≤ |c| * ‖a‖ ^ 3 := by
  have he : (rankOneCubic a c).form u u u = c * (inner ℝ a u) ^ 3 := by
    rw [rankOneCubic_apply]; ring
  rw [he, abs_mul, abs_pow]
  have hb : |inner ℝ a u| ≤ ‖a‖ := by simpa only [hu, mul_one] using abs_real_inner_le_norm a u
  gcongr

/-- A genuine unit vector attains the exact rank-one cubic budget.
Article: main_krylov, apA:lem:angle.
Proof: normalize the real Riesz vector of the rank-one coordinate. -/
theorem rankOneCubic_attains (a : E) (ha : a ≠ 0) (c : ℝ) :
    ∃ u : E, ‖u‖ = 1 ∧ |(rankOneCubic a c).form u u u| = |c| * ‖a‖ ^ 3 := by
  let u := ‖a‖⁻¹ • a
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), hn.ne']
  have hi : inner ℝ a u = ‖a‖ := by
    simp only [u, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  refine ⟨u, hu, ?_⟩
  rw [rankOneCubic_apply, hi]
  have he : c * ‖a‖ * ‖a‖ * ‖a‖ = c * ‖a‖ ^ 3 := by ring
  rw [he, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]

/-- The dual vector of a nonzero oldest step.
Article: main_krylov, apA:lem:angle, phi=s0/norm(s0)^2. -/
def dualStep (s : E) : E := (‖s‖ ^ 2)⁻¹ • s

/-- The true dual step pairs to one with its original step.
Article: main_krylov, apA:lem:angle. Proof: normalize the actual squared norm. -/
theorem dualStep_pair (s : E) (hs : s ≠ 0) : inner ℝ (dualStep s) s = 1 := by
  simp only [dualStep, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hs))

/-- The genuine dual-step norm is the reciprocal step norm.
Article: main_krylov, apA:lem:angle. Proof: take the norm of its explicit scalar multiple. -/
theorem dualStep_norm (s : E) (hs : s ≠ 0) : ‖dualStep s‖ = ‖s‖⁻¹ := by
  rw [dualStep, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  field_simp

/-- Orthogonal actual step columns have the printed oldest dual coordinate.
Article: main_krylov, apA:lem:angle, S-transpose phi equals the oldest coordinate vector.
Proof: the true self pairing is one and every other pairing vanishes by orthogonality. -/
theorem dualStep_window_coordinates {p : ℕ} (s : Fin p → E) (i₀ : Fin p)
    (hs : s i₀ ≠ 0) (horth : ∀ j, j ≠ i₀ → inner ℝ (s i₀) (s j) = 0) :
    ∀ j, inner ℝ (dualStep (s i₀)) (s j) = if j = i₀ then 1 else 0 := by
  intro j
  by_cases hj : j = i₀
  · subst j
    rw [ite_eq_left rfl]
    exact dualStep_pair _ hs
  · rw [ite_eq_right hj]
    simp only [dualStep, inner_smul_left, conj_trivial, horth j hj, mul_zero]

/-- Genuine affine Hessian secants differ by the actual cubic midpoint slice.
Article: main_krylov, apA:lem:angle.
Proof: integrate both actual affine Hessian fields at their true midpoints
and subtract using linearity of the real third derivative. -/
theorem affine_secant_diagonal (H₀ : E →L[ℝ] E →L[ℝ] ℝ) (T : SymmetricCubic E)
    (a u b v s : E) :
    (averagedDerivative (fun x => H₀ + T.form x) b v -
      averagedDerivative (fun x => H₀ + T.form x) a u) s s =
        T.form ((b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u)) s s := by
  rw [averagedHessian_affine H₀ T.form b v, averagedHessian_affine H₀ T.form a u]
  simp only [sub_apply, add_apply, map_sub]
  ring

/-- The true diagonal secant error obeys the article's injective-norm bound.
Article: main_krylov, apA:lem:angle.
Proof: apply the proved Banach diagonal-to-mixed identity to the actual
midpoint contraction, with the two genuine step slots retained. -/
theorem affine_secant_diagonal_bound [FiniteDimensional ℝ E]
    (H₀ : E →L[ℝ] E →L[ℝ] ℝ) (T : SymmetricCubic E) (C : ℝ)
    (hT : ∀ h : E, ‖h‖ = 1 → |T.form h h h| ≤ C) (a u b v s : E) :
    |(averagedDerivative (fun x => H₀ + T.form x) b v -
      averagedDerivative (fun x => H₀ + T.form x) a u) s s| ≤
        C * ‖s‖ ^ 2 * ‖(b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u)‖ := by
  rw [affine_secant_diagonal]
  exact (krylov.Tensor.cubic_diagonal_bound T C hT _ s s).trans_eq (by ring)

/-- Actual hidden-family secant drift is the cubic midpoint contraction, including zero cases.
Article: main_krylov, apA:lem:angle.
Proof: both genuine averaged affine Hessians are their actual midpoint values. -/
theorem hidden_midpoint_diagonal (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ a u b v s : E) :
    (averagedDerivative (hiddenHessian φ c x₀) b v -
      averagedDerivative (hiddenHessian φ c x₀) a u) s s =
      c * φ ((b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u)) * (φ s) ^ 2 := by
  rw [averaged_hiddenHessian, averaged_hiddenHessian]
  simp only [sub_apply, hiddenHessian, coordinateSquare, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, smul_eq_mul]
  ring

/-- The actual final and oldest midpoints have the printed hidden coordinate difference.
Article: main_krylov, apA:lem:angle, the final consistency identity.
Proof: expand the true linear coordinate at both actual midpoints. -/
theorem hidden_midpoint_coordinate (φ : E →L[ℝ] ℝ) (x₀ xₚ s u : E)
    (hx : φ (xₚ - x₀) = 1) (hs : φ s = 1) :
    φ ((xₚ + (1 / 2 : ℝ) • u) - (x₀ + (1 / 2 : ℝ) • s)) =
      (1 + φ u) / 2 := by
  rw [map_sub] at hx
  simp only [map_sub, map_add, map_smul, smul_eq_mul, hs]
  linarith

/-- The nonzero hidden cubic has exactly the source's normalized cosine error.
Article: main_krylov, apA:lem:angle.
Proof: use the actual midpoint contraction, the true dual-step pairing and
its proved norm. The nonzero hypotheses are precisely the divided expression's domain. -/
theorem hidden_normalized_cosine (s : E) (hs : s ≠ 0) (c : ℝ) (hc : c ≠ 0)
    (x₀ a u b v : E)
    (hd : (b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u) ≠ 0) :
    let φ := innerSL ℝ (dualStep s)
    let d := (b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u)
    |(averagedDerivative (hiddenHessian φ c x₀) b v -
      averagedDerivative (hiddenHessian φ c x₀) a u) s s| /
        ((|c| * ‖dualStep s‖ ^ 3) * ‖s‖ ^ 2 * ‖d‖) =
      |inner ℝ (dualStep s) d| / (‖dualStep s‖ * ‖d‖) := by
  dsimp only
  rw [hidden_midpoint_diagonal]
  change |c * inner ℝ (dualStep s) _ * (inner ℝ (dualStep s) s) ^ 2| / _ = _
  rw [dualStep_pair s hs, one_pow, mul_one, abs_mul, dualStep_norm s hs]
  have hsn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr hs
  have hdn : ‖(b + (1 / 2 : ℝ) • v) - (a + (1 / 2 : ℝ) • u)‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have hcn : |c| ≠ 0 := abs_ne_zero.mpr hc
  field_simp

end
end krylov.Functions

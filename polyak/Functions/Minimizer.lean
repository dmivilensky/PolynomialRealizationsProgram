import polyak.Functions.Normalization
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
Article: the unique minimizer in the original class.
Proof: a normalized gradient gives a contraction; its fixed point is stationary,
and the strong tangent bound proves global minimality and uniqueness.
-/

noncomputable section

namespace polyak

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: strong convexity makes the actual gradient strongly monotone.
Proof: add the first-order strong convexity inequalities. -/
theorem SmoothStronglyConvex.gradient_strong_monotone {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (x y : E) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪gradient f x - gradient f y, x - y⟫_ℝ := by
  have hxy := hf.tangent_lower x y
  have hyx := hf.tangent_lower y x
  rw [norm_sub_rev y x] at hxy
  simp only [inner_sub_left, inner_sub_right] at hxy hyx ⊢
  linarith

/-- Article: stationarity characterizes the global minimum.
Proof: apply the strong tangent inequality and Fermat's theorem. -/
theorem SmoothStronglyConvex.minimizer_iff {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (x : E) :
    (∀ y, f x ≤ f y) ↔ gradient f x = 0 := by
  constructor
  · intro hx
    have hmin : IsLocalMin f x := Filter.Eventually.of_forall hx
    have hz := hmin.hasFDerivAt_eq_zero (hf.differentiable x).hasFDerivAt
    have hg := (hf.differentiable x).hasGradientAt
    apply (InnerProductSpace.toDual ℝ E).injective
    simpa only [map_zero, toDual_gradient] using hz
  · intro hg y
    have h := hf.tangent_lower x y
    rw [hg, inner_zero_left] at h
    nlinarith [sq_nonneg ‖y - x‖, hf.mu_pos]

/-- Article: every objective in the class has a stationary point in an arbitrary
complete real Hilbert space. Proof: Banach's fixed point theorem applied to the
nonexpansive normalized gradient scaled by (L − μ)/(L + μ). -/
theorem SmoothStronglyConvex.exists_stationary {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) : ∃ x, gradient f x = 0 := by
  have hM : 0 < L - μ := sub_pos.mpr hf.mu_lt_L
  have hS : 0 < L + μ := by linarith [hf.mu_pos, hf.mu_lt_L]
  let r : NNReal := ⟨(L - μ) / (L + μ), (div_pos hM hS).le⟩
  let T : E → E := fun x => (r : ℝ) • gradient (normalizeFunction μ L f) x
  have hcontract : ContractingWith r T := by
    refine ⟨?_, ?_⟩
    · change (L - μ) / (L + μ) < 1
      apply (div_lt_one hS).mpr
      linarith [hf.mu_pos]
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      have hlip := hf.normalized_gradient_lipschitz.dist_le_mul x y
      simp only [dist_eq_norm, NNReal.coe_one, one_mul] at hlip ⊢
      dsimp [T]
      rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      change |(L - μ) / (L + μ)| * _ ≤ (L - μ) / (L + μ) * _
      rw [abs_of_pos (div_pos hM hS)]
      exact mul_le_mul_of_nonneg_left hlip r.2
  let x := hcontract.fixedPoint T
  have hx := hcontract.fixedPoint_isFixedPt
  change (r : ℝ) • gradient (normalizeFunction μ L f) x = x at hx
  rw [(hasGradientAt_normalize hf.differentiable x).gradient, smul_sub, smul_smul, smul_smul] at hx
  have hc : (r : ℝ) * ((L + μ) / (L - μ)) = 1 := by
    change (L - μ) / (L + μ) * ((L + μ) / (L - μ)) = 1
    field_simp [ne_of_gt hM, ne_of_gt hS]
  rw [hc, one_smul] at hx
  have hz : ((r : ℝ) * (2 / (L - μ))) • gradient f x = 0 := by
    exact sub_eq_self.mp hx
  refine ⟨x, (smul_eq_zero.mp hz).resolve_left ?_⟩
  exact ne_of_gt (mul_pos (div_pos hM hS) (div_pos (by norm_num) hM))

/-- Article: existence and uniqueness of the genuine minimizer.
Proof: existence follows from contraction; strong gradient monotonicity gives
uniqueness without any finite-dimensional compactness assumption. -/
theorem SmoothStronglyConvex.existsUnique_minimizer {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) : ∃! x, ∀ y, f x ≤ f y := by
  obtain ⟨x, hx⟩ := hf.exists_stationary
  refine ⟨x, (hf.minimizer_iff x).mpr hx, ?_⟩
  intro y hy
  have hy0 := (hf.minimizer_iff y).mp hy
  have h := hf.gradient_strong_monotone y x
  rw [hy0, hx, sub_self, inner_zero_left] at h
  have hn : ‖y - x‖ = 0 := by
    by_contra hn
    exact (not_lt_of_ge h) (mul_pos hf.mu_pos (sq_pos_of_ne_zero hn))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end polyak

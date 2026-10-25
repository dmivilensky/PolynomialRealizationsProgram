import polyak.Functions.Descent
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Module

/-!
Article: Lemma normalization and its proof in Appendix A.
Use: equivalence of the genuine original and normalized function classes.
-/

noncomputable section

namespace polyak

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: quadratic-linear operations on genuine derivatives. Proof: the
Fréchet product and addition rules followed by Riesz representation. -/
theorem hasGradientAt_quadratic_add {f : E → ℝ} {g x : E}
    (hf : HasGradientAt f g x) (a b : ℝ) :
    HasGradientAt (fun y => a / 2 * ‖y‖ ^ 2 + b * f y) (a • x + b • g) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (a / 2)).add
    (hf.hasFDerivAt.const_mul b)) using 1
  ext z
  simp [InnerProductSpace.toDual_apply_apply]
  ring

/-- Article: reduced convex function f₀ = f − μ‖·‖²/2. -/
def reducedFunction (μ : ℝ) (f : E → ℝ) (x : E) : ℝ := f x - μ / 2 * ‖x‖ ^ 2

/-- Article: normalized potential ψ. Use: the forward normalization map. -/
def normalizeFunction (μ L : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ((L + μ) / 2 * ‖x‖ ^ 2 - 2 * f x) / (L - μ)

/-- Article: inverse normalization. Use: turn a normalized potential into a
smooth strongly convex objective without imposing second derivatives. -/
def denormalizeFunction (μ L : ℝ) (ψ : E → ℝ) (x : E) : ℝ :=
  (L + μ) / 4 * ‖x‖ ^ 2 - (L - μ) / 2 * ψ x

/-- Article: gradient of the normalized potential. Proof: derivative rules. -/
theorem hasGradientAt_normalize {f : E → ℝ} {μ L : ℝ}
    (hf : Differentiable ℝ f) (x : E) :
    HasGradientAt (normalizeFunction μ L f)
      (((L + μ) / (L - μ)) • x - (2 / (L - μ)) • gradient f x) x := by
  convert hasGradientAt_quadratic_add (hf x).hasGradientAt
    ((L + μ) / (L - μ)) (-2 / (L - μ)) using 1
  · funext y
    dsimp [normalizeFunction]
    ring
  · module

/-- Article: gradient of the inverse normalization. Proof: derivative rules. -/
theorem hasGradientAt_denormalize {ψ : E → ℝ} {μ L : ℝ}
    (hψ : Differentiable ℝ ψ) (x : E) :
    HasGradientAt (denormalizeFunction μ L ψ)
      (((L + μ) / 2) • x - ((L - μ) / 2) • gradient ψ x) x := by
  convert hasGradientAt_quadratic_add (hψ x).hasGradientAt
    ((L + μ) / 2) (-(L - μ) / 2) using 1
  · funext y
    dsimp [denormalizeFunction]
    ring
  · module

/-- Article: reduced gradients satisfy cocoercivity with constant L − μ.
Proof: subtract the quadratic from the strong lower and smooth upper models,
then apply the convex descent argument. -/
theorem SmoothStronglyConvex.reduced_cocoercive {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (x y : E) :
    ‖(gradient f x - μ • x) - (gradient f y - μ • y)‖ ^ 2 ≤
      (L - μ) * ⟪(gradient f x - μ • x) - (gradient f y - μ • y), x - y⟫_ℝ := by
  apply cocoercive_of_quadratic_bounds (f := reducedFunction μ f)
    (g := fun z => gradient f z - μ • z) (sub_pos.mpr hf.mu_lt_L) (x := x) (y := y)
  · intro z w
    have h := hf.tangent_lower z w
    dsimp [reducedFunction]
    simp only [inner_sub_left, inner_smul_left, norm_sub_sq_real] at h ⊢
    simp only [inner_sub_right, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial] at h ⊢
    have hi : ⟪w, z⟫_ℝ = ⟪z, w⟫_ℝ := real_inner_comm _ _
    rw [hi] at h
    try simp only [hi] at *
    nlinarith
  · intro z w
    have h := descent_inequality (fun z => (hf.differentiable z).hasGradientAt)
      hf.grad_lipschitz z w
    dsimp [reducedFunction]
    simp only [inner_sub_left, inner_smul_left, norm_sub_sq_real] at h ⊢
    simp only [inner_sub_right, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial] at h ⊢
    have hi : ⟪w, z⟫_ℝ = ⟪z, w⟫_ℝ := real_inner_comm _ _
    rw [hi] at h
    try simp only [hi] at *
    nlinarith

/-- Article: normalization preserves the global Lipschitz bound before
centering. Proof: reduced cocoercivity and the Hilbert reflection identity. -/
theorem SmoothStronglyConvex.normalized_gradient_lipschitz {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) :
    LipschitzWith 1 (gradient (normalizeFunction μ L f)) := by
  have hgrad := hasGradientAt_normalize hf.differentiable (μ := μ) (L := L)
  have hM : 0 < L - μ := sub_pos.mpr hf.mu_lt_L
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul]
  rw [(hgrad x).gradient, (hgrad y).gradient]
  have heq : ((L + μ) / (L - μ)) • x - (2 / (L - μ)) • gradient f x -
      (((L + μ) / (L - μ)) • y - (2 / (L - μ)) • gradient f y) =
      (x - y) - (2 / (L - μ)) •
        ((gradient f x - μ • x) - (gradient f y - μ • y)) := by
    have hc : (L + μ) / (L - μ) = 1 + (2 / (L - μ)) * μ := by
      field_simp [ne_of_gt hM]
      ring
    rw [hc]
    module
  rw [heq]
  exact norm_reflection_le hM _ _ (hf.reduced_cocoercive x y)

/-- Article: normalization has a nonexpansive genuine gradient.
Proof: reduced cocoercivity and the Hilbert reflection identity. -/
theorem CenteredSmoothStronglyConvex.normalize {μ L : ℝ} {f : E → ℝ}
    (hf : CenteredSmoothStronglyConvex μ L f) :
    NormalizedSmooth (normalizeFunction μ L f) := by
  have hgrad := hasGradientAt_normalize hf.differentiable (μ := μ) (L := L)
  refine ⟨fun x => (hgrad x).differentiableAt,
    hf.toSmoothStronglyConvex.normalized_gradient_lipschitz, ?_, ?_⟩
  · simp [normalizeFunction, hf.value_zero]
  · rw [(hgrad 0).gradient, hf.gradient_zero]
    simp

/-- Article: the inverse map gives the original genuine class.
Proof: the descent upper model of ψ gives strong convexity of f; triangle
inequality gives L smoothness. -/
theorem NormalizedSmooth.denormalize {μ L : ℝ} {ψ : E → ℝ}
    (hψ : NormalizedSmooth ψ) (hμ : 0 < μ) (hμL : μ < L) :
    CenteredSmoothStronglyConvex μ L (denormalizeFunction μ L ψ) := by
  have hgrad := hasGradientAt_denormalize hψ.differentiable (μ := μ) (L := L)
  have hM : 0 < L - μ := sub_pos.mpr hμL
  have hsum : 0 < L + μ := by linarith
  have hLip (x y : E) : ‖gradient ψ x - gradient ψ y‖ ≤ 1 * ‖x - y‖ := by
    simpa [dist_eq_norm] using hψ.grad_lipschitz.dist_le_mul x y
  refine ⟨⟨hμ, hμL, fun x => (hgrad x).differentiableAt, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    have h := descent_inequality (fun x => (hψ.differentiable x).hasGradientAt) hLip x y
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hM)
    rw [(hgrad x).gradient]
    dsimp [denormalizeFunction]
    simp only [inner_sub_left, inner_smul_left, inner_sub_right,
      norm_sub_sq_real, real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial] at hm ⊢
    have hi : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm _ _
    rw [hi]
    nlinarith
  · intro x y
    rw [(hgrad x).gradient, (hgrad y).gradient]
    have heq : ((L + μ) / 2) • x - ((L - μ) / 2) • gradient ψ x -
        (((L + μ) / 2) • y - ((L - μ) / 2) • gradient ψ y) =
        ((L + μ) / 2) • (x - y) - ((L - μ) / 2) • (gradient ψ x - gradient ψ y) := by module
    rw [heq]
    calc
      _ ≤ ‖((L + μ) / 2) • (x - y)‖ + ‖((L - μ) / 2) • (gradient ψ x - gradient ψ y)‖ := norm_sub_le _ _
      _ = (L + μ) / 2 * ‖x - y‖ + (L - μ) / 2 * ‖gradient ψ x - gradient ψ y‖ := by
        simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hsum),
          abs_of_nonneg (le_of_lt hM)]
      _ ≤ (L + μ) / 2 * ‖x - y‖ + (L - μ) / 2 * ‖x - y‖ := by gcongr; simpa using hLip x y
      _ = L * ‖x - y‖ := by ring
  · simp [denormalizeFunction, hψ.value_zero]
  · rw [(hgrad 0).gradient, hψ.gradient_zero]
    simp

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Article: the two normalization maps are inverse on the original class.
Proof: cancel the nonzero scale L − μ in the value formula. -/
theorem denormalize_normalize {μ L : ℝ} (hμL : μ < L) (f : E → ℝ) :
    denormalizeFunction μ L (normalizeFunction μ L f) = f := by
  funext x
  dsimp [denormalizeFunction, normalizeFunction]
  field_simp [ne_of_gt (sub_pos.mpr hμL)]
  ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Article: the two normalization maps are inverse on S.
Proof: cancel the nonzero scale L − μ in the value formula. -/
theorem normalize_denormalize {μ L : ℝ} (hμL : μ < L) (ψ : E → ℝ) :
    normalizeFunction μ L (denormalizeFunction μ L ψ) = ψ := by
  funext x
  dsimp [denormalizeFunction, normalizeFunction]
  field_simp [ne_of_gt (sub_pos.mpr hμL)]
  ring

/-- Article: the zero potential belongs to S. Use: nonemptiness in every Hilbert
space and the quadratic examples for finite horizon suprema. -/
theorem normalizedSmooth_zero : NormalizedSmooth (fun _ : E => 0) := by
  refine ⟨differentiable_const 0, ?_, rfl, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [gradient_fun_const]
  · exact gradient_fun_const 0 0

/-- Article: two-sided Taylor bound for S. Proof: apply descent to −ψ.
Use: convexification in the interpolation necessity direction. -/
theorem NormalizedSmooth.lower_model {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) (x y : E) :
    ψ x + ⟪gradient ψ x, y - x⟫_ℝ - 1 / 2 * ‖y - x‖ ^ 2 ≤ ψ y := by
  have hg (z : E) : HasGradientAt (fun w => -ψ w) (-gradient ψ z) z := by
    convert hasGradientAt_quadratic_add (hψ.differentiable z).hasGradientAt 0 (-1) using 1 <;> simp
  have hlip (z w : E) : ‖(-gradient ψ z) - (-gradient ψ w)‖ ≤ 1 * ‖z - w‖ := by
    simpa [dist_eq_norm, norm_neg_add] using hψ.grad_lipschitz.dist_le_mul z w
  have h := descent_inequality hg hlip x y
  simp only [inner_neg_left] at h
  linarith

/-- Article: Lemma normalization, as a genuine bijection of function classes.
Proof: the analytic forward and inverse class theorems and the exact value
identities. Use: transport results without replacing the original class. -/
def normalizationEquiv {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) :
    {f : E → ℝ // CenteredSmoothStronglyConvex μ L f} ≃
      {ψ : E → ℝ // NormalizedSmooth ψ} where
  toFun f := ⟨normalizeFunction μ L f.1, f.2.normalize⟩
  invFun ψ := ⟨denormalizeFunction μ L ψ.1, ψ.2.denormalize hμ hμL⟩
  left_inv f := Subtype.ext (denormalize_normalize hμL f.1)
  right_inv ψ := Subtype.ext (normalize_denormalize hμL ψ.1)

end polyak

import polyak.Functions.Minimizer
import polyak.Functions.Convexity

/-!
Article: reduction to a minimizer at the origin and scale normalization.
Use: preserve the actual objective class under translations and positive
objective scalings, with explicit derivative identities.
-/

noncomputable section

namespace polyak

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: recenter an objective and its value at a chosen point. -/
def centerObjective (f : E → ℝ) (a x : E) : ℝ := f (a + x) - f a

/-- Article: recentering preserves the genuine derivative.
Proof: chain rule for translation followed by subtraction of a constant. -/
theorem hasGradientAt_centerObjective {f : E → ℝ} (hf : Differentiable ℝ f) (a x : E) :
    HasGradientAt (polyak.centerObjective f a) (gradient f (a + x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hf (a + x)).hasGradientAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_add a)).sub_const (f a)) using 1 <;>
    rfl

/-- Article: translation preserves the original smooth strongly convex class.
Proof: translate both points in the two class inequalities. -/
theorem SmoothStronglyConvex.centerObjective {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (a : E) :
    SmoothStronglyConvex μ L (polyak.centerObjective f a) := by
  have hg := hasGradientAt_centerObjective hf.differentiable a
  refine ⟨hf.mu_pos, hf.mu_lt_L, fun x => (hg x).differentiableAt, ?_, ?_⟩
  · intro x y
    rw [(hg x).gradient]
    have h := hf.tangent_lower (a + x) (a + y)
    dsimp [polyak.centerObjective]
    simp only [add_sub_add_left_eq_sub] at h
    linarith
  · intro x y
    rw [(hg x).gradient, (hg y).gradient]
    simpa using hf.grad_lipschitz (a + x) (a + y)

/-- Article: every original objective can be centered at its genuine minimum.
Proof: contraction gives the minimizer; the translation chain rule sends its
gradient to zero and subtraction sets its value to zero. -/
theorem SmoothStronglyConvex.exists_centered {μ L : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) :
    ∃ a, (∀ y, f a ≤ f y) ∧ CenteredSmoothStronglyConvex μ L (polyak.centerObjective f a) := by
  obtain ⟨a, ha⟩ := hf.exists_stationary
  refine ⟨a, (hf.minimizer_iff a).mpr ha, hf.centerObjective a, ?_, ?_⟩
  · simp [polyak.centerObjective]
  · rw [(hasGradientAt_centerObjective hf.differentiable a 0).gradient]
    simpa using ha

/-- Article: positive objective scaling scales both curvature parameters.
Proof: scalar derivative rule and multiplication of the defining inequalities. -/
theorem SmoothStronglyConvex.mul_pos {μ L c : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (hc : 0 < c) :
    SmoothStronglyConvex (c * μ) (c * L) (fun x => c * f x) := by
  have hg (x : E) : HasGradientAt (fun y => c * f y) (c • gradient f x) x := by
    simpa using hasGradientAt_quadratic_add (hf.differentiable x).hasGradientAt 0 c
  refine ⟨_root_.mul_pos hc hf.mu_pos, mul_lt_mul_of_pos_left hf.mu_lt_L hc,
    fun x => (hg x).differentiableAt, ?_, ?_⟩
  · intro x y
    rw [(hg x).gradient]
    have h := mul_le_mul_of_nonneg_left (hf.tangent_lower x y) hc.le
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    nlinarith
  · intro x y
    rw [(hg x).gradient, (hg y).gradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    calc
      c * ‖gradient f x - gradient f y‖ ≤ c * (L * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hf.grad_lipschitz x y) hc.le
      _ = (c * L) * ‖x - y‖ := by ring

/-- Article: positive scaling is an equivalence, not a class relaxation.
Proof: apply the forward scaling theorem with reciprocal scale. -/
theorem smoothStronglyConvex_mul_pos_iff {μ L c : ℝ} {f : E → ℝ} (hc : 0 < c) :
    SmoothStronglyConvex (c * μ) (c * L) (fun x => c * f x) ↔
      SmoothStronglyConvex μ L f := by
  refine ⟨fun hf => ?_, fun hf => hf.mul_pos hc⟩
  have h := hf.mul_pos (inv_pos.mpr hc)
  simpa [ne_of_gt hc] using h

/-- Article: normalize the amplitude of points while preserving both curvature
parameters. Use: reduce nonzero initial displacements to unit norm. -/
def rescaleObjective (r : ℝ) (f : E → ℝ) (x : E) : ℝ := f (r • x) / r ^ 2

/-- Article: the actual gradient under amplitude normalization.
Proof: the chain rule and the reciprocal square value factor. -/
theorem hasGradientAt_rescaleObjective {f : E → ℝ} (hf : Differentiable ℝ f)
    {r : ℝ} (hr : 0 < r) (x : E) :
    HasGradientAt (rescaleObjective r f) ((1 / r) • gradient f (r • x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (((hf (r • x)).hasGradientAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul r)).mul_const (1 / r ^ 2)) using 1
  · funext y
    dsimp [rescaleObjective]
    ring
  · ext z
    simp
    field_simp [ne_of_gt hr]

/-- Article: amplitude normalization preserves the genuine original class.
Proof: the scalar cancels exactly in the strong tangent and gradient bounds. -/
theorem SmoothStronglyConvex.rescaleObjective {μ L r : ℝ} {f : E → ℝ}
    (hf : SmoothStronglyConvex μ L f) (hr : 0 < r) :
    SmoothStronglyConvex μ L (polyak.rescaleObjective r f) := by
  have hg := hasGradientAt_rescaleObjective hf.differentiable hr
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  refine ⟨hf.mu_pos, hf.mu_lt_L, fun x => (hg x).differentiableAt, ?_, ?_⟩
  · intro x y
    rw [(hg x).gradient]
    have h := hf.tangent_lower (r • x) (r • y)
    rw [← smul_sub, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
    dsimp [polyak.rescaleObjective]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    apply (mul_le_mul_iff_left₀ hr2).mp
    field_simp [ne_of_gt hr]
    nlinarith
  · intro x y
    rw [(hg x).gradient, (hg y).gradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hr)]
    have h := hf.grad_lipschitz (r • x) (r • y)
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr] at h
    calc
      _ ≤ (1 / r) * (L * (r * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left h (div_pos (by norm_num) hr).le
      _ = L * ‖x - y‖ := by field_simp

omit [CompleteSpace E] in
/-- Article: amplitude normalization is invertible.
Proof: the reciprocal state scaling cancels both value factors. -/
theorem rescaleObjective_inv {r : ℝ} (hr : 0 < r) (f : E → ℝ) :
    rescaleObjective (1 / r) (rescaleObjective r f) = f := by
  funext x
  dsimp [rescaleObjective]
  rw [smul_smul]
  simp [ne_of_gt hr]

end polyak

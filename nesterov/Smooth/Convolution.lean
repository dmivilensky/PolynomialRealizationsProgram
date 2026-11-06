import polyak.Functions.Transforms
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.L2Space

/-!
Article: Remark `rem:uniform-smoothness`, Appendix A.
Use: convolution preserves both original curvature constants, with its actual
Hilbert gradient computed by differentiation under the integral.
-/

noncomputable section
namespace nesterov.Smooth
open MeasureTheory Filter Set Metric
open scoped Topology InnerProductSpace Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : Measure E) [m.IsAddHaarMeasure]

/-- Smooth averaging uses a normalized nonnegative bump of compact support. -/
def average (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, φ.normed m z * f (x-z) ∂m

/-- The candidate derivative is the average of the genuine gradients. -/
def averageGradient (φ : ContDiffBump (0 : E)) (f : E → ℝ) (x : E) : E :=
  ∫ z, φ.normed m z • gradient f (x-z) ∂m

omit [CompleteSpace E] in
private theorem weighted_integrable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : ContDiffBump (0 : E)) {a : E → F} (ha : Continuous a) :
    Integrable (fun z => φ.normed m z • a z) m := by
  exact ((φ.continuous_normed.smul ha).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.smul_right))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_gradient {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) : Continuous (gradient f) := by
  have hL : 0 ≤ L := by linarith [hf.mu_pos,hf.mu_lt_L]
  have h : LipschitzWith (Real.toNNReal L) (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm,Real.coe_toNNReal L hL] using hf.grad_lipschitz x y
  exact h.continuous

omit [CompleteSpace E] in
/-- The average of a continuous objective is infinitely differentiable. -/
theorem average_contDiff (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : Continuous f) : ContDiff ℝ ∞ (average m φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hf.locallyIntegrable

/-- Differentiation under a compactly supported integral gives the actual gradient. -/
theorem hasGradientAt_average (φ : ContDiffBump (0 : E)) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (x₀ : E) :
    HasGradientAt (average m φ f) (averageGradient m φ f x₀) x₀ := by
  have hgc := continuous_gradient hf
  let F' : E → E → E →L[ℝ] ℝ := fun x z =>
    φ.normed m z • InnerProductSpace.toDual ℝ E (gradient f (x-z))
  have hderiv (x z : E) : HasFDerivAt (fun y => φ.normed m z * f (y-z)) (F' x z) x := by
    simpa [F',smul_eq_mul] using
      (((hf.differentiable (x-z)).hasGradientAt.hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z)).const_mul (φ.normed m z))
  have hF_int : Integrable (fun z => φ.normed m z * f (x₀-z)) m := by
    exact weighted_integrable m φ (hf.differentiable.continuous.comp (by fun_prop))
  have hF'_int : Integrable (F' x₀) m :=
    weighted_integrable m φ ((InnerProductSpace.toDual ℝ E).continuous.comp
      (hgc.comp (by fun_prop)))
  have hbint : Integrable (fun z => φ.normed m z * (‖gradient f (x₀-z)‖+L)) m := by
    exact weighted_integrable m φ (((hgc.comp (by fun_prop)).norm).add continuous_const)
  have hd : HasFDerivAt (average m φ f) (∫ z, F' x₀ z ∂m) x₀ := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds _ zero_lt_one)
      (bound := fun z => φ.normed m z * (‖gradient f (x₀-z)‖+L))
    · exact Eventually.of_forall (fun x =>
        (φ.continuous_normed.mul (hf.differentiable.continuous.comp (by fun_prop))).aestronglyMeasurable)
    · exact hF_int
    · exact hF'_int.aestronglyMeasurable
    · filter_upwards with z x hx
      dsimp [F']
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed (μ := m) z)]
      rw [(InnerProductSpace.toDual ℝ E).norm_map]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed (μ := m) z)
      have hb := hf.grad_lipschitz (x-z) (x₀-z)
      rw [sub_sub_sub_cancel_right] at hb
      have hx' : ‖x-x₀‖ ≤ 1 := by exact (mem_ball_iff_norm.mp hx).le
      have hL : 0 ≤ L := by linarith [hf.mu_pos,hf.mu_lt_L]
      have hn := norm_le_norm_add_norm_sub' (gradient f (x-z)) (gradient f (x₀-z))
      nlinarith [mul_le_mul_of_nonneg_left hx' hL]
    · exact hbint
    · exact Eventually.of_forall (fun z x _ => hderiv x z)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  ext y
  rw [ContinuousLinearMap.integral_apply hF'_int]
  dsimp [averageGradient,F']
  simp only [smul_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
  rw [real_inner_comm]
  have hi := integral_inner (𝕜 := ℝ)
    (weighted_integrable m φ (a := fun z : E => gradient f (x₀-z))
      (hgc.comp (by fun_prop))) y
  simpa only [inner_smul_right,real_inner_comm y,
    mul_comm] using hi.symm


/-- The derivative of the averaged objective is its averaged gradient. -/
theorem gradient_average (φ : ContDiffBump (0 : E)) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (x : E) :
    gradient (average m φ f) x = averageGradient m φ f x :=
  (hasGradientAt_average m φ hf x).gradient

private theorem integral_gradient_inner (φ : ContDiffBump (0 : E)) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (x d : E) :
    (∫ z, φ.normed m z * ⟪gradient f (x-z),d⟫_ℝ ∂m) =
      ⟪averageGradient m φ f x,d⟫_ℝ := by
  have hi := integral_inner (𝕜 := ℝ)
    (weighted_integrable m φ (a := fun z : E => gradient f (x-z))
      ((continuous_gradient hf).comp (by fun_prop))) d
  simpa only [averageGradient,inner_smul_right,real_inner_comm d] using hi

/-- Averaging keeps the original strong-convexity and smoothness constants exactly. -/
theorem average_class (φ : ContDiffBump (0 : E)) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) :
    polyak.SmoothStronglyConvex μ L (average m φ f) := by
  have hfc := hf.differentiable.continuous
  have hgc := continuous_gradient hf
  have hint (x : E) : Integrable (fun z => φ.normed m z * f (x-z)) m :=
    weighted_integrable m φ (hfc.comp (by fun_prop))
  have hgint (x : E) : Integrable (fun z => φ.normed m z • gradient f (x-z)) m :=
    weighted_integrable m φ (hgc.comp (by fun_prop))
  have hiint (x d : E) : Integrable (fun z => φ.normed m z * ⟪gradient f (x-z),d⟫_ℝ) m :=
    weighted_integrable m φ ((hgc.comp (by fun_prop)).inner continuous_const)
  refine ⟨hf.mu_pos,hf.mu_lt_L,fun x => (hasGradientAt_average m φ hf x).differentiableAt,?_,?_⟩
  · intro x y
    rw [gradient_average m φ hf]
    have hbound (z : E) :
        φ.normed m z*f (x-z) + φ.normed m z*⟪gradient f (x-z),y-x⟫_ℝ +
          φ.normed m z*(μ/2*‖y-x‖^2) ≤ φ.normed m z*f (y-z) := by
      have h := mul_le_mul_of_nonneg_left (hf.tangent_lower (x-z) (y-z))
        (φ.nonneg_normed (μ := m) z)
      rw [sub_sub_sub_cancel_right] at h
      nlinarith
    have h := integral_mono
      (((hint x).add (hiint x (y-x))).add (φ.integrable_normed.mul_const (μ/2*‖y-x‖^2)))
      (hint y) hbound
    have he1 := integral_add ((hint x).add (hiint x (y-x)))
      (φ.integrable_normed (μ := m) |>.mul_const (μ/2*‖y-x‖^2))
    have he2 := integral_add (hint x) (hiint x (y-x))
    simp only [Pi.add_apply] at h he1 he2
    rw [he1,he2,integral_gradient_inner m φ hf,
      integral_mul_const,φ.integral_normed,one_mul] at h
    exact h
  · intro x y
    rw [gradient_average m φ hf,gradient_average m φ hf]
    unfold averageGradient
    rw [← integral_sub (hgint x) (hgint y)]
    calc
      _ ≤ ∫ z, ‖φ.normed m z • gradient f (x-z) -
          φ.normed m z • gradient f (y-z)‖ ∂m := norm_integral_le_integral_norm _
      _ ≤ ∫ z, φ.normed m z * (L*‖x-y‖) ∂m := by
        apply integral_mono ((hgint x).sub (hgint y)).norm
          (φ.integrable_normed.mul_const _)
        intro z
        simp only [Pi.sub_apply]
        rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed (μ := m) z)]
        have h := hf.grad_lipschitz (x-z) (y-z)
        rw [sub_sub_sub_cancel_right] at h
        exact mul_le_mul_of_nonneg_left h (φ.nonneg_normed (μ := m) z)
      _ = L*‖x-y‖ := by rw [integral_mul_const,φ.integral_normed,one_mul]

/-- The actual gradient changes uniformly by at most L times the averaging radius. -/
theorem average_gradient_error (φ : ContDiffBump (0 : E)) {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (x : E) :
    ‖gradient (average m φ f) x-gradient f x‖ ≤ L*φ.rOut := by
  rw [gradient_average m φ hf]
  rw [← dist_eq_norm]
  change dist ((φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ,m] gradient f) x) (gradient f x) ≤ _
  apply φ.dist_normed_convolution_le (continuous_gradient hf).aestronglyMeasurable
  intro y hy
  have hL : 0 ≤ L := by linarith [hf.mu_pos,hf.mu_lt_L]
  exact (show dist (gradient f y) (gradient f x) ≤ L*dist y x by
    simpa only [dist_eq_norm] using hf.grad_lipschitz y x).trans
    (mul_le_mul_of_nonneg_left hy.le hL)

include m in
/-- Centered C∞ objectives approximate a centered C¹,¹ objective uniformly in gradient,
with no loss in either curvature parameter. The radius and error are explicit. -/
theorem exists_centered_contDiff_radius {μ L r : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (hr : 0 < r) :
    ∃ g : E → ℝ, polyak.CenteredSmoothStronglyConvex μ L g ∧ ContDiff ℝ ∞ g ∧
      ∀ x, ‖gradient g x-gradient f x‖ ≤ L*r*(1+L/μ) := by
  let φ : ContDiffBump (0 : E) := ⟨r/2,r,half_pos hr,half_lt_self hr⟩
  let F := average m φ f
  have hF : polyak.SmoothStronglyConvex μ L F := average_class m φ hf.toSmoothStronglyConvex
  have hFs : ContDiff ℝ ∞ F := average_contDiff m φ hf.differentiable.continuous
  obtain ⟨a,ha⟩ := hF.exists_stationary
  have hL : 0 < L := hf.mu_pos.trans hf.mu_lt_L
  have he (x : E) : ‖gradient F x-gradient f x‖ ≤ L*r :=
    average_gradient_error m φ hf.toSmoothStronglyConvex x
  have ha_bound : ‖a‖ ≤ L*r/μ := by
    have hm := hF.gradient_strong_monotone a 0
    rw [ha,sub_zero,zero_sub,inner_neg_left] at hm
    have hc := real_inner_le_norm (-gradient F 0) a
    simp only [inner_neg_left,norm_neg] at hc
    have he0 := he 0
    rw [hf.gradient_zero,sub_zero] at he0
    have hm' : μ*‖a‖^2 ≤ L*r*‖a‖ := by
      nlinarith [mul_le_mul_of_nonneg_right he0 (norm_nonneg a)]
    by_cases hz : ‖a‖ = 0
    · rw [hz]
      exact div_nonneg (mul_nonneg hL.le hr.le) hf.mu_pos.le
    · apply (le_div_iff₀ hf.mu_pos).mpr
      have hn : 0 < ‖a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  let g := polyak.centerObjective F a
  have hgdiff := polyak.hasGradientAt_centerObjective hF.differentiable a
  refine ⟨g,⟨hF.centerObjective a,?_,?_⟩,?_,?_⟩
  · simp [g,polyak.centerObjective]
  · rw [(hgdiff 0).gradient]
    simpa using ha
  · exact (hFs.comp (contDiff_const.add contDiff_id)).sub contDiff_const
  · intro x
    rw [(hgdiff x).gradient]
    calc
      ‖gradient F (a+x)-gradient f x‖ ≤
          ‖gradient F (a+x)-gradient F x‖+‖gradient F x-gradient f x‖ := by
        rw [show gradient F (a+x)-gradient f x =
          (gradient F (a+x)-gradient F x)+(gradient F x-gradient f x) by abel]
        exact norm_add_le _ _
      _ ≤ L*‖a‖+L*r := by
        have hl := hF.grad_lipschitz (a+x) x
        rw [add_sub_cancel_right] at hl
        exact add_le_add hl (he x)
      _ ≤ L*(L*r/μ)+L*r := by gcongr
      _ = L*r*(1+L/μ) := by ring

include m in
/-- Every prescribed positive uniform gradient accuracy is attainable by a genuine
centered C∞ objective in exactly the original μ,L class. -/
theorem exists_centered_contDiff_approx {μ L ε : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) (hε : 0 < ε) :
    ∃ g : E → ℝ, polyak.CenteredSmoothStronglyConvex μ L g ∧ ContDiff ℝ ∞ g ∧
      ∀ x, ‖gradient g x-gradient f x‖ < ε := by
  have hL : 0 < L := hf.mu_pos.trans hf.mu_lt_L
  have hμ : 0 < μ := hf.mu_pos
  have hC : 0 < L*(1+L/μ) := mul_pos hL (by positivity)
  obtain ⟨g,hg,hs,he⟩ := exists_centered_contDiff_radius m hf
    (div_pos hε (mul_pos (by norm_num : (0:ℝ)<2) hC))
  refine ⟨g,hg,hs,fun x => (he x).trans_lt ?_⟩
  have hmul : L*(ε/(2*(L*(1+L/μ))))*(1+L/μ) = ε/2 := by
    field_simp [ne_of_gt hL,ne_of_gt hf.mu_pos,ne_of_gt (by positivity : 0 < 1+L/μ)]
  rw [hmul]
  linarith

end nesterov.Smooth

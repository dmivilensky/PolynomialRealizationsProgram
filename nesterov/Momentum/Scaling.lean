import nesterov.Momentum.Normalization
import nesterov.Momentum.QueryRates

/-!
Article: §2 normalization L=1 and accelerated-scaling convention.
Use: an exact bijection of original function classes transports the complete
actual latent execution, all finite-horizon suprema and all three distance factors.
-/
namespace nesterov.Momentum
noncomputable section
open Set Filter
open scoped Topology

section Objectives
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Positive normalization is an equivalence of the exact original classes. -/
theorem normalized_objective_iff {μ L : ℝ} (hL : 0<L) (f : E → ℝ) :
    polyak.SmoothStronglyConvex (μ/L) 1 (fun x => f x/L) ↔
      polyak.SmoothStronglyConvex μ L f := by
  have hh := polyak.smoothStronglyConvex_mul_pos_iff
    (μ:=μ) (L:=L) (f:=f) (inv_pos.mpr hL)
  simpa [div_eq_mul_inv,mul_comm,ne_of_gt hL] using hh

theorem centered_normalized_objective_iff {μ L : ℝ} (hL : 0<L) (f : E → ℝ) :
    polyak.CenteredSmoothStronglyConvex (μ/L) 1 (fun x => f x/L) ↔
      polyak.CenteredSmoothStronglyConvex μ L f := by
  constructor
  · intro hf
    have hclass := (normalized_objective_iff hL f).mp hf.toSmoothStronglyConvex
    refine ⟨hclass,?_,?_⟩
    · exact (div_eq_zero_iff.mp hf.value_zero).resolve_right (ne_of_gt hL)
    · have hh := gradient_normalized hclass.differentiable L (0:E)
      rw [hf.gradient_zero] at hh
      exact (smul_eq_zero.mp hh.symm).resolve_left (one_div_ne_zero (ne_of_gt hL))
  · intro hf
    refine ⟨(normalized_objective_iff hL f).mpr hf.toSmoothStronglyConvex,?_,?_⟩
    · simp [hf.value_zero]
    · rw [gradient_normalized hf.differentiable L,hf.gradient_zero,smul_zero]

theorem centered_unnormalized_objective {μ L : ℝ} (hL : 0<L) {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex (μ/L) 1 f) :
    polyak.CenteredSmoothStronglyConvex μ L (fun x => L*f x) := by
  apply (centered_normalized_objective_iff hL _).mp
  simpa only [mul_div_cancel_left₀ _ (ne_of_gt hL)] using hf

theorem gradient_unnormalized {f : E → ℝ} (hf : Differentiable ℝ f) (L : ℝ) (x : E) :
    gradient (fun y => L*f y) x=L • gradient f x := by
  simpa using (polyak.hasGradientAt_quadratic_add (hf x).hasGradientAt 0 L).gradient

end Objectives

/-- Normalize the objective and step, preserving the complete latent history. -/
def normalizedRun {β τ h μ L : ℝ} (hh : h≠0) (hL : 0<L)
    (r : Rates.HilbertRun (method β τ h hh) μ L) :
    Rates.HilbertRun (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1 where
  Carrier := r.Carrier
  f x := r.f x/L
  admissible := (centered_normalized_objective_iff hL r.f).mpr r.admissible
  w := r.w
  trajectory := by
    apply (method_trajectory_iff _ _ _ _ _ _).mpr
    intro n
    have hr := (method_trajectory_iff _ _ _ _ _ _).mp r.trajectory n
    rw [gradient_normalized r.admissible.differentiable L,smul_smul]
    have hc : h*L*(1/L)=h := by field_simp
    rw [hc]
    exact hr

/-- The inverse objective/step scaling, on exactly the same latent history. -/
def unnormalizedRun {β τ h μ L : ℝ} (hh : h≠0) (hL : 0<L)
    (r : Rates.HilbertRun (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1) :
    Rates.HilbertRun (method β τ h hh) μ L where
  Carrier := r.Carrier
  f x := L*r.f x
  admissible := centered_unnormalized_objective hL r.admissible
  w := r.w
  trajectory := by
    apply (method_trajectory_iff _ _ _ _ _ _).mpr
    intro n
    have hr := (method_trajectory_iff _ _ _ _ _ _).mp r.trajectory n
    rw [gradient_unnormalized r.admissible.differentiable L,smul_smul]
    exact hr

/-- The free-state ratio sets agree before taking any supremum or time limit. -/
theorem ratios_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    Rates.ratios (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1 n=
      Rates.ratios (method β τ h hh) μ L n := by
  ext x
  constructor
  · rintro ⟨r,hr,hx⟩
    exact ⟨unnormalizedRun hh hL r,hr,hx⟩
  · rintro ⟨r,hr,hx⟩
    exact ⟨normalizedRun hh hL r,hr,hx⟩

theorem envelope_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    Rates.envelope (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1 n=
      Rates.envelope (method β τ h hh) μ L n := by
  simp only [Rates.envelope,ratios_normalized β τ h μ L hh hL n]

theorem restRatios_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    Rates.restRatios (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1 n=
      Rates.restRatios (method β τ h hh) μ L n := by
  ext x
  constructor
  · rintro ⟨r,hfd,hr,hz,hx⟩
    exact ⟨unnormalizedRun hh hL r,hfd,hr,hz,hx⟩
  · rintro ⟨r,hfd,hr,hz,hx⟩
    exact ⟨normalizedRun hh hL r,hfd,hr,hz,hx⟩

theorem restEnvelope_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    Rates.restEnvelope (method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))) (μ/L) 1 n=
      Rates.restEnvelope (method β τ h hh) μ L n := by
  simp only [Rates.restEnvelope,restRatios_normalized β τ h μ L hh hL n]

theorem queryRestRatios_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    queryRestRatios β τ (h*L) (mul_ne_zero hh (ne_of_gt hL)) (μ/L) 1 n=
      queryRestRatios β τ h hh μ L n := by
  ext x
  constructor
  · rintro ⟨r,hfd,hr,hz,hx⟩
    refine ⟨unnormalizedRun hh hL r,hfd,hr,hz,?_⟩
    change x=‖(method β τ h hh).query r.w n‖/‖r.w 0‖
    rw [method_query]
    simpa only [method_query] using hx
  · rintro ⟨r,hfd,hr,hz,hx⟩
    refine ⟨normalizedRun hh hL r,hfd,hr,hz,?_⟩
    change x=‖(method β τ (h*L) (mul_ne_zero hh (ne_of_gt hL))).query r.w n‖/‖r.w 0‖
    rw [method_query]
    simpa only [method_query] using hx

theorem queryRestEnvelope_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) (n : ℕ) :
    queryRestEnvelope β τ (h*L) (mul_ne_zero hh (ne_of_gt hL)) (μ/L) 1 n=
      queryRestEnvelope β τ h hh μ L n := by
  simp only [queryRestEnvelope,queryRestRatios_normalized β τ h μ L hh hL n]

/-- The complete uniform root factor is invariant under the exact L=1 normalization. -/
theorem momentumRate_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) :
    momentumRate β τ (h*L) (mul_ne_zero hh (ne_of_gt hL)) (μ/L) 1=
      momentumRate β τ h hh μ L := by
  unfold momentumRate Rates.rate Rates.exponent
  simp only [envelope_normalized β τ h μ L hh hL]

theorem momentumRestRate_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) :
    momentumRestRate β τ (h*L) (mul_ne_zero hh (ne_of_gt hL)) (μ/L) 1=
      momentumRestRate β τ h hh μ L := by
  unfold momentumRestRate Rates.restRate
  simp only [restEnvelope_normalized β τ h μ L hh hL]

theorem queryRestRate_normalized (β τ h μ L : ℝ) (hh : h≠0) (hL : 0<L) :
    queryRestRate β τ (h*L) (mul_ne_zero hh (ne_of_gt hL)) (μ/L) 1=
      queryRestRate β τ h hh μ L := by
  unfold queryRestRate
  simp only [queryRestEnvelope_normalized β τ h μ L hh hL]

end
end nesterov.Momentum

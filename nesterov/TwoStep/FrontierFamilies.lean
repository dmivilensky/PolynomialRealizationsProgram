import nesterov.TwoStep.FrontierOptimization
import nesterov.TwoStep.AsymptoticsPhysical
import nesterov.TwoStep.BoundaryRates
import nesterov.TwoStep.Bulk

/-! Actual stable families realizing the complete fixed-extrapolation arc,
and the supremum of the strict bulk constants. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem raw_linear_beta_limit (θ : ℝ) :
    Tendsto (fun ε : ℝ=>(1-(1-θ*ε))/ε) (𝓝[>] (0:ℝ)) (𝓝 θ) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0<ε at hε
  field_simp
  ring

private theorem raw_sqrt_step_limit (y : ℝ) :
    Tendsto (fun ε : ℝ=>y-Real.sqrt ε) (𝓝[>] (0:ℝ)) (𝓝 y) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  simpa only [Real.sqrt_zero,sub_zero] using (tendsto_const_nhds (x:=y)).sub he.sqrt

def frontierFamily {θ τ : ℝ} (hθ : 0<θ) (hτ : 0<τ) :
    Scaling ℝ (𝓝[>] (0:ℝ)) θ (frontierStep τ) τ :=
  fromRawLimits (fun ε=>1-θ*ε) (fun _=>τ) (fun ε=>frontierStep τ-Real.sqrt ε)
    hθ (frontierStep_pos hτ.le) hτ (raw_linear_beta_limit θ)
    (raw_sqrt_step_limit (frontierStep τ)) tendsto_const_nhds

theorem frontierFamily_parameters {θ τ : ℝ} (hθ : 0<θ) (hτ : 0<τ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),((frontierFamily hθ hτ).tuning ε).beta=1-θ*ε ∧
      ((frontierFamily hθ hτ).tuning ε).tau=τ ∧
        ((frontierFamily hθ hτ).tuning ε).stepSize=frontierStep τ-Real.sqrt ε :=
  fromRawLimits_parameters _ _ _ hθ (frontierStep_pos hτ.le) hτ _ _ _

@[simp] theorem frontierFamily_epsilon {θ τ : ℝ} (hθ : 0<θ) (hτ : 0<τ) :
    (frontierFamily hθ hτ).epsilon=id := rfl

theorem frontierFamily_margin_atTop {θ τ : ℝ} (hθ : 0<θ) (hτ : 0<τ) :
    Tendsto (frontierFamily hθ hτ).stabilityMargin (𝓝[>] (0:ℝ)) atTop := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hepos : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ),0<ε := self_mem_nhdsWithin
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [Real.sqrt_zero] using he.sqrt,
      hepos.mono fun _ hε=>Real.sqrt_pos.mpr hε⟩
  have hi := (tendsto_inv_nhdsGT_zero.comp hs).atTop_mul_const (show 0<1+2*τ by linarith)
  apply hi.congr'
  filter_upwards [frontierFamily_parameters hθ hτ,self_mem_nhdsWithin] with ε hp hε
  have hep : 0<ε := hε
  have hsp : Real.sqrt ε≠0 := (Real.sqrt_pos.mpr hep).ne'
  have hD : 1+2*τ≠0 := by positivity
  have hY : frontierStep τ*(1+2*τ)=4 := div_mul_cancel₀ _ hD
  change (Real.sqrt ε)⁻¹*(1+2*τ)=
    (4-((frontierFamily hθ hτ).tuning ε).stepSize*
      (1+2*((frontierFamily hθ hτ).tuning ε).tau))/ε
  rw [hp.2.1,hp.2.2]
  have hn : 4-(frontierStep τ-Real.sqrt ε)*(1+2*τ)=(1+2*τ)*Real.sqrt ε := by nlinarith only [hY]
  rw [hn]
  field_simp
  nlinarith only [Real.sq_sqrt hep.le]

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem stable_of_margin_atTop (hs : Tendsto F.stabilityMargin l atTop) :
    ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1 := by
  filter_upwards [hs.eventually_gt_atTop (2*θ+2),
    F.theta_tendsto.eventually (eventually_lt_nhds (show θ<θ+1 by linarith)),
    F.stability_gap_exact,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hs ht hg he he1
  change F.thetaAt a<θ+1 at ht
  have hgap : 0<largestCurvatureGap (F.tuning a) := by
    rw [hg]
    exact mul_pos (by linarith) he
  rw [largestCurvatureGap_eq] at hgap
  apply ((F.tuning a).stable_iff (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)).mpr
  simpa only [mul_one] using (show (F.tuning a).stepSize*(1+2*(F.tuning a).tau)<
    2*(1+(F.tuning a).beta) by linarith)

end Scaling

theorem frontierFamily_stable {θ τ : ℝ} (hθ : 0<θ) (hτ : 0<τ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),((frontierFamily hθ hτ).tuning ε).Stable (ε^2) 1 :=
  (frontierFamily hθ hτ).stable_of_margin_atTop (frontierFamily_margin_atTop hθ hτ)

/-- Every point of the entire source arc has one explicit stable realizing family. -/
theorem frontier_arc_attained {τ θ : ℝ} (hτ : 1/2<τ)
    (hl : 2*Real.sqrt (frontierStep τ)≤θ) (hu : θ≤3*Real.sqrt (frontierStep τ/2)) :
    ∃ F : Scaling ℝ (𝓝[>] (0:ℝ)) θ (frontierStep τ) τ,F.epsilon=id ∧
      (∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) ∧
        Tendsto (fun ε=>(1-F.rate ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 (Flow.cQ θ (frontierStep τ))) ∧
        Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (θ/3)) ∧
        Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (θ/3)) := by
  have hτp : 0<τ := by linarith
  have hY := frontierStep_pos hτp.le
  have hθ : 0<θ := (mul_pos (by norm_num) (Real.sqrt_pos.mpr hY)).trans_le hl
  let F := frontierFamily hθ hτp
  have hm := frontierFamily_margin_atTop hθ hτp
  have hstable := frontierFamily_stable hθ hτp
  have hboundary : frontierStep τ*(1+2*τ)=4 := div_mul_cancel₀ _ (by positivity)
  have hq := F.quadratic_boundary_coefficient_tendsto_infinite hm
  have hF := F.boundary_coefficients_tendsto_infinite rfl hstable hτ hboundary hm
  have hthird := Flow.cF_eq_third_of_damping_le_optimal hθ hY hu
  rw [hthird] at hF
  exact ⟨F,rfl,hstable,hq,hF.1,hF.2⟩

end
end nesterov.TwoStep

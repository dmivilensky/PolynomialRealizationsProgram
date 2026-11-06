import nesterov.TwoStep.FrontierFamilies

/-! Frontier(iii): the supremum refers to actual stable families and their
literal full-class and from-rest limits. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def bulkFamily {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ) :
    Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ :=
  fromRawLimits (fun ε=>1-θ*ε) (fun _=>τ) (fun _=>y)
    hθ hy hτ (raw_linear_beta_limit θ) tendsto_const_nhds tendsto_const_nhds

@[simp] theorem bulkFamily_epsilon {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ) :
    (bulkFamily hθ hy hτ).epsilon=id := rfl

theorem bulkFamily_stable {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ)
    (hm : y*(1+2*τ)<4) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),((bulkFamily hθ hy hτ).tuning ε).Stable (ε^2) 1 := by
  let F := bulkFamily hθ hy hτ
  have hh := F.bulk_roots_eventually_lt (Flow.cQ_pos hθ hy) hm
  filter_upwards [hh] with ε hε
  intro lam hlam z hz
  simpa only [zero_mul,sub_zero] using hε lam hlam z hz

def attainableBulkConstants (τ : ℝ) : Set ℝ :=
  {a | ∃ θ y : ℝ,y*(1+2*τ)<4 ∧ ∃ F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ,
    F.epsilon=id ∧ (∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) ∧
      Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 a) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 a)}

theorem attainableBulkConstants_eq {τ : ℝ} (hτ : 1/2<τ) :
    attainableBulkConstants τ=bulkConstantSet τ := by
  ext a
  constructor
  · rintro ⟨θ,y,hm,F,he,hs,hf,_⟩
    have hb := F.bulk_coefficients_tendsto he hs hτ hm
    exact ⟨θ,y,F.theta_pos,F.step_pos,hm,tendsto_nhds_unique hf hb.1⟩
  · rintro ⟨θ,y,hθ,hy,hm,rfl⟩
    have hτp : 0<τ := by linarith
    let F := bulkFamily hθ hy hτp
    have hs := bulkFamily_stable hθ hy hτp hm
    have hb := F.bulk_coefficients_tendsto rfl hs hτ hm
    exact ⟨θ,y,hm,F,rfl,hs,hb.1,hb.2⟩

/-- The actual-family supremum and its nonattainment in the strict bulk. -/
theorem actual_bulk_frontier {τ : ℝ} (hτ : 1/2<τ) :
    IsLUB (attainableBulkConstants τ) (Real.sqrt (frontierStep τ/2)) ∧
      Real.sqrt (frontierStep τ/2)∉attainableBulkConstants τ ∧
        Real.sqrt (frontierStep τ/2)<1 := by
  rw [attainableBulkConstants_eq hτ]
  refine ⟨bulk_constants_isLUB (by linarith),bulk_supremum_not_attained (by linarith),?_⟩
  have hy := frontierStep_lt_two hτ
  have hh := Real.sqrt_lt_sqrt (show 0≤frontierStep τ/2 by positivity [frontierStep_pos (by linarith : 0≤τ)])
    (show frontierStep τ/2<(1:ℝ) by linarith)
  simpa only [Real.sqrt_one] using hh

namespace Scaling
variable {θ τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ (frontierStep τ) τ)

/-- The optimal bulk supremum is reached at the boundary by every source
family with optimal damping and an alternating constant above the stated cutoff. -/
theorem optimal_boundary_constants (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {s : ℝ} (hτ : 1/2<τ) (hθ : θ=3*Real.sqrt (frontierStep τ/2))
    (hmargin : Tendsto F.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 s)) (hsθ : 2*θ<s)
    (hcut : 2*θ+(4*τ/(1+2*τ))*(θ/3)≤s) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (frontierStep τ/2))) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (frontierStep τ/2))) := by
  have hb : frontierStep τ*(1+2*τ)=4 := div_mul_cancel₀ _ (by linarith)
  have hh := F.boundary_coefficients_tendsto he hs hτ hb hmargin hsθ
  have hvalue : min (Flow.cF θ (frontierStep τ)) (alternatingConstant θ τ s)=Real.sqrt (frontierStep τ/2) := by
    rw [hθ]
    apply (boundary_optimum_iff (by linarith : 0<τ)).mpr
    simpa only [hθ] using hcut
  rwa [hvalue] at hh

end Scaling
end
end nesterov.TwoStep

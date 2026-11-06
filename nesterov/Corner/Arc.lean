import nesterov.Corner.Consequences
import nesterov.Corner.Kappa
import nesterov.TwoStep.FrontierFamilies

/-! Actual physical corner families attain the entire half-step arc,
including the stated maximal-quadratic example. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

private theorem affine_epsilon_limit (a b : ℝ) :
    Tendsto (fun ε : ℝ=>a-b*ε) (𝓝[>] (0:ℝ)) (𝓝 a) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  simpa only [mul_zero,sub_zero] using (tendsto_const_nhds (x:=a)).sub (he.const_mul b)

def cornerFamily {θ : ℝ} (hθ : 0<θ) (a b : ℝ) :
    Scaling ℝ (𝓝[>] (0:ℝ)) θ 2 (1/2) :=
  fromRawLimits (fun ε=>1-θ*ε) (fun ε=>1/2-a*ε) (fun ε=>2-b*ε)
    hθ (by norm_num) (by norm_num) (raw_linear_beta_limit θ)
    (affine_epsilon_limit 2 b) (affine_epsilon_limit (1/2) a)

theorem cornerFamily_parameters {θ : ℝ} (hθ : 0<θ) (a b : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),((cornerFamily hθ a b).tuning ε).beta=1-θ*ε ∧
      ((cornerFamily hθ a b).tuning ε).tau=1/2-a*ε ∧
        ((cornerFamily hθ a b).tuning ε).stepSize=2-b*ε :=
  fromRawLimits_parameters _ _ _ hθ (by norm_num) (by norm_num) _ _ _

theorem cornerFamily_coordinates {θ : ℝ} (hθ : 0<θ) (a b : ℝ) :
    Tendsto (cornerFamily hθ a b).cornerA (𝓝[>] (0:ℝ)) (𝓝 a) ∧
      Tendsto (cornerFamily hθ a b).cornerB (𝓝[>] (0:ℝ)) (𝓝 b) := by
  constructor
  · apply tendsto_const_nhds.congr'
    filter_upwards [cornerFamily_parameters hθ a b,self_mem_nhdsWithin] with ε hp he
    have he0 : ε≠0 := (show 0<ε from he).ne'
    unfold Scaling.cornerA
    rw [hp.2.1]
    change a=(1/2-(1/2-a*ε))/ε
    field_simp
    ring
  · apply tendsto_const_nhds.congr'
    filter_upwards [cornerFamily_parameters hθ a b,self_mem_nhdsWithin] with ε hp he
    have he0 : ε≠0 := (show 0<ε from he).ne'
    unfold Scaling.cornerB
    rw [hp.2.2]
    change b=(2-(2-b*ε))/ε
    field_simp
    ring

theorem arc_family_coefficients {θ : ℝ} (hθ : 0<θ) (hθ3 : θ≤3) :
    let F := cornerFamily hθ 0 (2*θ)
    Tendsto F.fullCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 (θ/3)) ∧
      Tendsto F.restCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 (θ/3)) ∧
      Tendsto (fun ε=>(1-F.rate ε)/F.epsilon ε) (𝓝[>] (0:ℝ)) (𝓝 (Flow.cQ θ 2)) := by
  let F := cornerFamily hθ 0 (2*θ)
  have ha := (cornerFamily_coordinates hθ 0 (2*θ)).1
  have hb := (cornerFamily_coordinates hθ 0 (2*θ)).2
  have hfull := F.corner_flow_region ha hb hθ3 (by linarith) (by linarith)
  have hmargin : θ<2*0+2*θ := by linarith
  have hstable := F.corner_eventually_stable ha hb hmargin
  have hq := F.quadratic_boundary_coefficient_tendsto (by norm_num : (1/2:ℝ)≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) hstable (F.corner_margin_tendsto ha hb)
  have hcpi : alternatingConstant θ (1/2) (4*0+2*(2*θ))=2*θ := by
    unfold alternatingConstant
    norm_num
    ring
  rw [hcpi,min_eq_left (by linarith [Flow.cQ_le_half θ 2] : Flow.cQ θ 2≤2*θ)] at hq
  exact ⟨hfull.1,hfull.2,hq⟩

theorem arc_family_kappa {θ : ℝ} (hθ : 0<θ) (hθ3 : θ≤3) :
    let F := cornerFamily hθ 0 (2*θ)
    Tendsto F.fullKappaCoefficient atTop (𝓝 (θ/3)) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (θ/3)) ∧
      Tendsto F.quadraticKappaCoefficient atTop (𝓝 (Flow.cQ θ 2)) := by
  have h := arc_family_coefficients hθ hθ3
  have hfr := (cornerFamily hθ 0 (2*θ)).coefficientsAt_kappa_transport rfl h.1 h.2.1
  exact ⟨hfr.1,hfr.2,(cornerFamily hθ 0 (2*θ)).quadraticAt_kappa_transport rfl h.2.2⟩

theorem maximal_quadratic_corner_kappa :
    let F := cornerFamily (show 0<2*Real.sqrt 2 by positivity) 0 4
    Tendsto F.fullKappaCoefficient atTop (𝓝 (2*Real.sqrt 2/3)) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (2*Real.sqrt 2/3)) ∧
      Tendsto F.quadraticKappaCoefficient atTop (𝓝 (Real.sqrt 2)) := by
  let θ : ℝ := 2*Real.sqrt 2
  have hθ : 0<θ := by dsimp [θ];positivity
  let F := cornerFamily hθ 0 4
  have ha := (cornerFamily_coordinates hθ 0 4).1
  have hb := (cornerFamily_coordinates hθ 0 4).2
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hr := Real.sqrt_nonneg (2:ℝ)
  have hmargin : θ<2*0+4 := by dsimp [θ];nlinarith
  have hconc : 4*0+4≤2*θ := by dsimp [θ];nlinarith
  have hQ : Flow.cQ θ 2=Real.sqrt 2 := Flow.cQ_critical (by norm_num)
  have hcp : Corner.endpointConstant θ 0 4=θ/3 := by
    unfold Corner.endpointConstant Corner.cpi
    rw [hQ]
    rw [min_eq_left (by dsimp [θ];nlinarith : θ/3≤2*(2*0+4-θ))]
    apply min_eq_right_of_lt
    dsimp [θ]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)]
  have hf := F.corner_coefficients_of_concave ha hb hmargin hconc
  rw [hcp] at hf
  have hfr := F.coefficientsAt_kappa_transport rfl hf.1 hf.2
  have hq := F.quadratic_boundary_coefficient_tendsto (by norm_num : (1/2:ℝ)≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) (F.corner_eventually_stable ha hb hmargin)
    (F.corner_margin_tendsto ha hb)
  have hp : alternatingConstant θ (1/2) (4*0+2*4)=2*(4-θ) := by
    unfold alternatingConstant
    norm_num
    ring
  rw [hQ,hp,min_eq_left (by dsimp [θ];nlinarith : Real.sqrt 2≤2*(4-θ))] at hq
  exact ⟨hfr.1,hfr.2,F.quadraticAt_kappa_transport rfl hq⟩

end
end nesterov.TwoStep

import nesterov.Layer.ResultsLower
import nesterov.Layer.Upper
import nesterov.TwoStep.Kappa

/-! Matched full-class and from-rest layer constants, including the
minus-infinite deficit and literal condition-number limits. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem layer_coefficients_order :
    ∀ᶠ a in l,F.fullCoefficientAt a≤F.restCoefficientAt a := by
  filter_upwards [F.epsilon_pos,F.epsilon_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a he he1
  exact div_le_div_of_nonneg_right (sub_le_sub_left
    (Momentum.restRate_le_momentumRate (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau)
      (F.tuning a).step_pos.ne' (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)) 1) he.le

private theorem coefficients_tendsto_of_layer_bounds {m : ℝ}
    (hupper : ∀ c : ℝ,c<m → ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta
      (F.tuning a).tau (F.tuning a).stepSize (F.tuning a).step_pos.ne'
      (F.epsilon a^2) 1<1-c*F.epsilon a)
    (hceiling : ∀ b : ℝ,m<b → ∀ᶠ a in l,F.restCoefficientAt a≤b) :
    Tendsto F.fullCoefficientAt l (𝓝 m) ∧ Tendsto F.restCoefficientAt l (𝓝 m) := by
  have hlo (c : ℝ) (hc : c<m) :
      ∀ᶠ a in l,c<F.fullCoefficientAt a ∧ c<F.restCoefficientAt a := by
    filter_upwards [hupper c hc,F.epsilon_pos,F.layer_coefficients_order] with a ha he hcomp
    have hf : c<F.fullCoefficientAt a := (lt_div_iff₀ he).mpr (by
      change c*F.epsilon a<1-Momentum.momentumRate (F.tuning a).beta
        (F.tuning a).tau (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1
      linarith)
    exact ⟨hf,hf.trans_le hcomp⟩
  have hhi (b : ℝ) (hb : m<b) :
      ∀ᶠ a in l,F.fullCoefficientAt a<b ∧ F.restCoefficientAt a<b := by
    obtain ⟨d,hd,hdb⟩ := exists_between hb
    filter_upwards [hceiling d hd,F.layer_coefficients_order] with a ha hcomp
    exact ⟨(hcomp.trans ha).trans_lt hdb,ha.trans_lt hdb⟩
  constructor
  · exact tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.1,
      fun b hb=>(hhi b hb).mono fun _ h=>h.1⟩
  · exact tendsto_order.mpr ⟨fun c hc=>(hlo c hc).mono fun _ h=>h.2,
      fun b hb=>(hhi b hb).mono fun _ h=>h.2⟩

theorem layer_coefficients_tendsto_filter [l.IsCountablyGenerated] {B : ℝ}
    (hy2 : y<2) (hB : Tendsto F.layerDeficit l (𝓝 B)) (hBA : B<Layer.Astar θ y)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    Tendsto F.fullCoefficientAt l (𝓝 (Layer.constant θ y B)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Layer.constant θ y B)) := by
  apply F.coefficients_tendsto_of_layer_bounds
  · exact fun c hc=>F.layer_upper hy2 hB hBA hc
  · intro b hb
    by_cases hB0 : B≤0
    · rw [Layer.constant_of_nonpos hB0] at hb
      exact F.rest_coefficient_eventually_le_filter hstable hb
    · have hBp : 0<B := lt_of_not_ge hB0
      have hLpos := (Layer.Lambda_pos_iff F.theta_pos F.step_pos hy2).mpr hBA
      by_cases hq : Flow.cQ θ y≤Layer.Lambda θ y B/3
      · have hCF : Flow.cF θ y=Flow.cQ θ y := min_eq_right (by
          have hh := Layer.Lambda_le_theta (θ:=θ) (A:=B) F.step_pos hy2
          linarith)
        have hC : Layer.constant θ y B=Flow.cQ θ y := min_eq_left hq
        rw [hC] at hb
        exact F.rest_coefficient_eventually_le_filter hstable (by rwa [hCF])
      · have hC : Layer.constant θ y B=Layer.Lambda θ y B/3 := min_eq_right (le_of_not_ge hq)
        apply F.layer_rest_coefficient_eventually_le hy2 hBp hB hstable
        rw [max_eq_left hLpos.le]
        rwa [hC] at hb

theorem layer_coefficients_tendsto_filter_atBot [l.IsCountablyGenerated]
    (hy2 : y<2) (hB : Tendsto F.layerDeficit l atBot)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    Tendsto F.fullCoefficientAt l (𝓝 (Flow.cF θ y)) ∧
      Tendsto F.restCoefficientAt l (𝓝 (Flow.cF θ y)) :=
  F.coefficients_tendsto_of_layer_bounds (fun _ hc=>F.layer_upper_atBot hy2 hB hc)
    (fun _ hb=>F.rest_coefficient_eventually_le_filter hstable hb)

end
end nesterov.TwoStep.Scaling

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y (1/2))

theorem layer_coefficients_tendsto (he : F.epsilon=id) {B : ℝ}
    (hy2 : y<2) (hB : Tendsto F.layerDeficit (𝓝[>] (0:ℝ)) (𝓝 B))
    (hBA : B<Layer.Astar θ y)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Layer.constant θ y B)) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Layer.constant θ y B)) := by
  have hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (F.epsilon ε^2) 1 := by
    simpa only [he,id_eq] using hstable
  have h := F.layer_coefficients_tendsto_filter hy2 hB hBA hs
  have hf : F.fullCoefficientAt=F.fullCoefficient := by
    funext ε
    simp only [fullCoefficientAt,fullCoefficient,he,id_eq]
  have hr : F.restCoefficientAt=F.restCoefficient := by
    funext ε
    simp only [restCoefficientAt,restCoefficient,he,id_eq]
  rwa [hf,hr] at h

theorem layer_kappa_coefficients_tendsto (he : F.epsilon=id) {B : ℝ}
    (hy2 : y<2) (hB : Tendsto F.layerDeficit (𝓝[>] (0:ℝ)) (𝓝 B))
    (hBA : B<Layer.Astar θ y)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 (Layer.constant θ y B)) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (Layer.constant θ y B)) := by
  have h := F.layer_coefficients_tendsto he hy2 hB hBA hstable
  exact ⟨F.full_kappa_transport h.1,F.rest_kappa_transport h.2⟩

theorem layer_coefficients_tendsto_atBot (he : F.epsilon=id)
    (hy2 : y<2) (hB : Tendsto F.layerDeficit (𝓝[>] (0:ℝ)) atBot)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) := by
  have hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (F.epsilon ε^2) 1 := by
    simpa only [he,id_eq] using hstable
  have h := F.layer_coefficients_tendsto_filter_atBot hy2 hB hs
  have hf : F.fullCoefficientAt=F.fullCoefficient := by
    funext ε
    simp only [fullCoefficientAt,fullCoefficient,he,id_eq]
  have hr : F.restCoefficientAt=F.restCoefficient := by
    funext ε
    simp only [restCoefficientAt,restCoefficient,he,id_eq]
  rwa [hf,hr] at h

theorem layer_kappa_coefficients_tendsto_atBot (he : F.epsilon=id)
    (hy2 : y<2) (hB : Tendsto F.layerDeficit (𝓝[>] (0:ℝ)) atBot)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 (Flow.cF θ y)) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (Flow.cF θ y)) := by
  have h := F.layer_coefficients_tendsto_atBot he hy2 hB hstable
  exact ⟨F.full_kappa_transport h.1,F.rest_kappa_transport h.2⟩

end
end nesterov.TwoStep.Scaling

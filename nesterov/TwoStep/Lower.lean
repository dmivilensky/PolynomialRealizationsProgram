import nesterov.TwoStep.AsymptoticsBridge
import nesterov.TwoStep.QuadraticAsymptotics
import nesterov.Slow.Ceiling
import nesterov.Realization.RestQuadratic

/-! The sampled flow spectrum yields genuine fixed-dimension witnesses from
rest, and bounds the literal from-rest rate with its supremum before the limit. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Spectral Flow
open scoped Topology NNReal
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

def fullCoefficient (ε : ℝ) : ℝ :=
  (1-Momentum.momentumRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
    (F.tuning ε).step_pos.ne' (ε^2) 1)/ε

def restCoefficient (ε : ℝ) : ℝ :=
  (1-Momentum.momentumRestRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
    (F.tuning ε).step_pos.ne' (ε^2) 1)/ε

 theorem sampled_rest_witness_of_spread (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {c : ℝ} (W : SpreadWitness θ y c) (hcp : 0<c) (hb : 0≤θ-2*c) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ (f : EuclideanSpace ℝ (Fin (2*W.J+1))→ℝ)
        (x₀ : EuclideanSpace ℝ (Fin (2*W.J+1))),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
        ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-(c*ε)*N)*‖x₀‖≤
          ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
  let G := F.toSecondOrderFamily he
  have hfeas := Slow.sampled_flow_feasible G W hcp hb
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hfeas,F.toSecondOrderFamily_method_eq he,hs,hsmall,self_mem_nhdsWithin]
    with ε hw hmethod hstable hε1 hε0
  obtain ⟨v,hv,C,hvfeas,_,_⟩ := hw
  change G.method ε=_ at hmethod
  rw [hmethod] at hvfeas
  have hε : 0<ε := hε0
  have hμL : ε^2<1 := by nlinarith
  have H := Realization.exists_real_startup (F.tuning ε) (sq_pos_of_pos hε) hμL hstable v
    (fun j=>Phase.frequency (ε*W.spectrum.frequency j)) hv hvfeas
    (fun ht=>False.elim ((not_lt_of_ge (by nlinarith : -c*ε≤0)) ht))
  obtain ⟨lam,_,Y,f,_,hf,_,hx,_,c₀,hc₀,hbound⟩ := H
  have H' : ∃ (f : EuclideanSpace ℝ (Fin (2*Fintype.card (Fin W.J)+1))→ℝ)
      (x₀ : EuclideanSpace ℝ (Fin (2*Fintype.card (Fin W.J)+1))),
      polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
      ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-(c*ε)*N)*‖x₀‖≤
        ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
    refine ⟨f,_,hf,hx,c₀,hc₀,fun N=>?_⟩
    simpa only [show -(c*ε)*(N:ℝ)=(N:ℝ)*(-c*ε) by ring] using hbound N
  rw [Fintype.card_fin] at H'
  exact H'

 theorem sampled_rest_witness (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {c : ℝ} (hc : θ/3<c) (hcQ : c<cQ θ y) :
    ∃ J : ℕ,0<J ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ (f : EuclideanSpace ℝ (Fin (2*J+1))→ℝ)
        (x₀ : EuclideanSpace ℝ (Fin (2*J+1))),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
        ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-(c*ε)*N)*‖x₀‖≤
          ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
  obtain ⟨W⟩ := exists_spread F.theta_pos F.step_pos hc hcQ
  have hcp : 0<c := by linarith [F.theta_pos]
  have hb : 0≤θ-2*c := by linarith [(lt_cQ_iff θ y c).mp hcQ |>.1]
  exact ⟨W.J,W.J_pos,F.sampled_rest_witness_of_spread he hs W hcp hb⟩

 theorem sampled_rest_rate_lower (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {c : ℝ} (hc : θ/3<c) (hcQ : c<cQ θ y) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),Real.exp (-c*ε)≤
      Momentum.momentumRestRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
        (F.tuning ε).step_pos.ne' (ε^2) 1 := by
  obtain ⟨J,_,hw⟩ := F.sampled_rest_witness he hs hc hcQ
  filter_upwards [hw] with ε hε
  obtain ⟨f,x₀,hf,hx,c₀,hc₀,hbound⟩ := hε
  apply (Rates.exp_le_root_limsup_of_lower_bound (mul_pos hc₀ (norm_pos_iff.mpr hx)) _
    (Momentum.iterate_roots_bounded (F.tuning ε).step_pos.ne' hf hx)).trans
    (Momentum.iterate_root_limsup_le_restRate (F.tuning ε).step_pos.ne' hf hx)
  intro N
  rw [show (N:ℝ)*(-c*ε)=-(c*ε)*N by ring]
  calc
    _=c₀*Real.exp (-(c*ε)*N)*‖x₀‖ := by ring
    _≤_ := hbound N

 theorem rest_coefficient_eventually_le (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {a : ℝ} (ha : cF θ y<a) : ∀ᶠ ε in 𝓝[>] (0:ℝ),F.restCoefficient ε≤a := by
  by_cases hQ : cQ θ y≤θ/3
  · have hca : cQ θ y<a := by simpa only [cF,min_eq_right hQ] using ha
    have hquad := F.quadratic_coefficient_eventually_lt hca
    rw [he] at hquad
    filter_upwards [hquad,self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with ε hq hε0 hε1
    have hε : 0<ε := hε0
    have hμL : ε^2<1 := by nlinarith
    have hh := Momentum.quadraticRate_le_momentumRestRate (β:=(F.tuning ε).beta)
      (τ:=(F.tuning ε).tau) (F.tuning ε).step_pos (sq_pos_of_pos hε) hμL
    have hi := div_le_div_of_nonneg_right (sub_le_sub_left hh 1) hε.le
    exact hi.trans (by simpa only [rate,he,id_eq] using hq.le)
  · have hgap : θ/3<cQ θ y := lt_of_not_ge hQ
    have hta : θ/3<a := by simpa only [cF,min_eq_left hgap.le] using ha
    obtain ⟨c,hc,hcm⟩ := exists_between (lt_min hta hgap)
    have hca : c<a := hcm.trans_le (min_le_left _ _)
    have hcQ : c<cQ θ y := hcm.trans_le (min_le_right _ _)
    have hr := F.sampled_rest_rate_lower he hs hc hcQ
    have hl := (Slow.SecondOrderFamily.exponential_coefficient_limit c).eventually (eventually_lt_nhds hca)
    filter_upwards [hr,hl,self_mem_nhdsWithin] with ε hrate hexp hε
    exact (div_le_div_of_nonneg_right (show 1-Momentum.momentumRestRate (F.tuning ε).beta
      (F.tuning ε).tau (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' (ε^2) 1≤1-Real.exp (-c*ε) by linarith)
      hε.le).trans hexp.le

end
end nesterov.TwoStep.Scaling

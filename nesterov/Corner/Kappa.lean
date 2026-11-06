import nesterov.Corner.Rates

/-! Literal condition-number versions of the corner bounds. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

private theorem kappa_transport_identity {e : ℝ→ℝ} (he : e=id)
    (R : ℝ→ℝ→ℝ) {κ : ℝ} (hκ : 0<κ) :
    Real.sqrt κ*(1-R (Slow.epsilon κ) (1/κ))=
      (1-R (Slow.epsilon κ) (e (Slow.epsilon κ)^2))/e (Slow.epsilon κ) := by
  have hε : e (Slow.epsilon κ)=Slow.epsilon κ := congrFun he _
  have hμ : e (Slow.epsilon κ)^2=1/κ :=
    (congrArg (fun x : ℝ=>x^2) hε).trans (Slow.epsilon_sq hκ.le)
  calc
    _=(1-R (Slow.epsilon κ) (1/κ))/Slow.epsilon κ := (Slow.coefficient_kappa hκ).symm
    _=_ := congrArg₂ (fun n d : ℝ=>n/d)
      (congrArg (fun x : ℝ=>1-x) (congrArg (R (Slow.epsilon κ)) hμ)).symm hε.symm

theorem fullKappaCoefficient_eventually_eq (he : F.epsilon=id) :
    ∀ᶠ κ in atTop,F.fullKappaCoefficient κ=F.fullCoefficientAt (Slow.epsilon κ) := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  exact kappa_transport_identity he (fun ε μ=>Momentum.momentumRate (F.tuning ε).beta
    (F.tuning ε).tau (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' μ 1) hκ

theorem restKappaCoefficient_eventually_eq (he : F.epsilon=id) :
    ∀ᶠ κ in atTop,F.restKappaCoefficient κ=F.restCoefficientAt (Slow.epsilon κ) := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  exact kappa_transport_identity he (fun ε μ=>Momentum.momentumRestRate (F.tuning ε).beta
    (F.tuning ε).tau (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' μ 1) hκ

theorem coefficientsAt_kappa_transport (he : F.epsilon=id) {c : ℝ}
    (hf : Tendsto F.fullCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 c))
    (hr : Tendsto F.restCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 c) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 c) := by
  have hf' := hf.comp Slow.epsilon_tendsto
  have hr' := hr.comp Slow.epsilon_tendsto
  exact ⟨hf'.congr' ((F.fullKappaCoefficient_eventually_eq he).mono fun _ h=>h.symm),
    hr'.congr' ((F.restKappaCoefficient_eventually_eq he).mono fun _ h=>h.symm)⟩

def quadraticKappaCoefficient (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Quadratic.quadraticRate (1/κ) 1 (F.tuning (Slow.epsilon κ)).beta
    (F.tuning (Slow.epsilon κ)).tau (F.tuning (Slow.epsilon κ)).stepSize)

theorem quadraticAt_kappa_transport (he : F.epsilon=id) {c : ℝ}
    (hq : Tendsto (fun ε=>(1-F.rate ε)/F.epsilon ε) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto F.quadraticKappaCoefficient atTop (𝓝 c) := by
  have h : Tendsto (fun ε=>(1-F.rate ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 c) := by
    simpa only [he,id_eq] using hq
  apply (TwoStep.coefficient_tendsto_kappa h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [quadraticKappaCoefficient,rate,he,id_eq,Slow.epsilon_sq hκ.le]

variable (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ 2 (1/2))

theorem corner_kappa_bounds (he : F.epsilon=id) {a b : ℝ}
    (ha : Tendsto F.cornerA (𝓝[>] (0:ℝ)) (𝓝 a))
    (hb : Tendsto F.cornerB (𝓝[>] (0:ℝ)) (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b) :
    (min (Flow.cQ θ 2) (Corner.cLag θ a b):EReal)≤
      liminf (fun κ=>(F.fullKappaCoefficient κ:EReal)) atTop ∧
    liminf (fun κ=>(F.fullKappaCoefficient κ:EReal)) atTop≤
      limsup (fun κ=>(F.restKappaCoefficient κ:EReal)) atTop ∧
    limsup (fun κ=>(F.restKappaCoefficient κ:EReal)) atTop≤
      (min (Flow.cQ θ 2) (Corner.cDisc θ a b):EReal) := by
  have hf : (fun κ=>(F.fullKappaCoefficient κ:EReal)) =ᶠ[atTop]
      (fun κ=>(F.fullCoefficientAt (Slow.epsilon κ):EReal)) :=
    (F.fullKappaCoefficient_eventually_eq he).mono fun _ h=>congrArg (fun r : ℝ=>(r:EReal)) h
  have hr : (fun κ=>(F.restKappaCoefficient κ:EReal)) =ᶠ[atTop]
      (fun κ=>(F.restCoefficientAt (Slow.epsilon κ):EReal)) :=
    (F.restKappaCoefficient_eventually_eq he).mono fun _ h=>congrArg (fun r : ℝ=>(r:EReal)) h
  have hfl := (Filter.liminf_congr hf).trans
    (Slow.epsilon_liminf (fun ε : ℝ=>(F.fullCoefficientAt ε:EReal)))
  have hrl := (Filter.limsup_congr hr).trans
    (Slow.epsilon_limsup (fun ε : ℝ=>(F.restCoefficientAt ε:EReal)))
  rw [hfl,hrl]
  exact F.corner_coefficient_bounds ha hb hmargin hLag

theorem corner_kappa_constants (he : F.epsilon=id) {a b : ℝ}
    (ha : Tendsto F.cornerA (𝓝[>] (0:ℝ)) (𝓝 a))
    (hb : Tendsto F.cornerB (𝓝[>] (0:ℝ)) (𝓝 b))
    (hmargin : θ<2*a+b) (hLag : 0<Corner.cLag θ a b)
    (heq : min (Flow.cQ θ 2) (Corner.cLag θ a b)=
      min (Flow.cQ θ 2) (Corner.cDisc θ a b)) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (min (Flow.cQ θ 2) (Corner.cLag θ a b))) := by
  have h := F.corner_coefficients_tendsto ha hb hmargin hLag heq
  exact F.coefficientsAt_kappa_transport he h.1 h.2

end
end nesterov.TwoStep.Scaling

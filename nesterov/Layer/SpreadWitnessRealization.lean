import nesterov.Realization.StartupCoordinates
import nesterov.Realization.RestRate
import nesterov.TwoStep.MixedCriterion

/-! A finite feasible spectrum gives the literal all-horizon real witness
required in the layer. Its dimension may vary with the tuning. -/
namespace nesterov.TwoStep
noncomputable section
open Spectral Set
open scoped BigOperators NNReal

def RestLowerWitness (q : Momentum.Tuning) (μ L r : ℝ) (d : ℕ) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin d) → ℝ) (x₀ : EuclideanSpace ℝ (Fin d)),
    polyak.CenteredSmoothStronglyConvex μ L f ∧ x₀≠0 ∧
    ∃ c₀ : ℝ, 0<c₀ ∧ ∀ N : ℕ, c₀*r^N*‖x₀‖≤
      ‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ N‖

theorem finite_spectrum_rest_witness (q : Momentum.Tuning) {μ L r C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (hr : 0<r)
    {J : ℕ} (w : Fin J → ℝ≥0) (c : Fin J → Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair
      μ L (Real.log r)) (Real.log r) (finiteSpectrum w c hw) C)
    (hreserve : |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r))) :
    RestLowerWitness q μ L r (2*J+1) := by
  suffices h : RestLowerWitness q μ L r (2*Fintype.card (Fin J)+1) by
    simpa only [Fintype.card_fin] using h
  obtain ⟨lam,hlam,Y,f,hY,hf,hlim,hx,heq,c₀,hc₀,hbound⟩ :=
    Realization.exists_real_startup q hμ hμL hs w c hw hfeas (fun _=>hreserve)
  let x₀ := Realization.startupCoordinates (Fin J)
    (Realization.physical (finiteLatent w c (Real.log r)) q.beta q.tau q.stepSize lam Y 0)
  refine ⟨f,x₀,hf,hx,c₀,hc₀,fun N=>?_⟩
  have hex : Real.exp ((N:ℝ)*Real.log r)=r^N := by
    rw [Real.exp_nat_mul,Real.exp_log hr]
  simpa only [hex,Fintype.card_fin] using hbound N

theorem rest_rate_ge_of_finite_spectrum (q : Momentum.Tuning) {μ L r C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (hr : 0<r)
    {J : ℕ} (w : Fin J → ℝ≥0) (c : Fin J → Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair
      μ L (Real.log r)) (Real.log r) (finiteSpectrum w c hw) C)
    (hreserve : |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r))) :
    r≤Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  have hh := Realization.exp_le_momentumRestRate_of_feasible q hμ hμL hs
    w c hw hfeas (fun _=>hreserve)
  simpa only [Real.exp_log hr] using hh

end
end nesterov.TwoStep

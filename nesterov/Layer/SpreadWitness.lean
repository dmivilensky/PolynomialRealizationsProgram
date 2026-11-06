import nesterov.Layer.SpreadWitnessPrepared
import nesterov.Layer.SpreadWitnessRealization
import nesterov.Spread.HalfStep

/-! Article Lemma spreadwit: original moving-band symbol hypotheses produce
finite feasible spectra and actual real from-rest witnesses at every horizon. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Spectral Phase
open scoped Topology BigOperators NNReal

namespace Spread.PreparedBand
variable {a : SymbolPair} {t s η : ℝ} {K : ℕ}

theorem finite (D : Spread.PreparedBand a t K s η)
    (hs : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1) :
    ∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (q : J→Frequency) (hw : ∑ j,w j=1),
      (∀ j,Real.arccos (q j:ℝ)∈Spread.sourceBand K s) ∧
      ∃ C : ℝ,Feasible a t (finiteSpectrum w q hw) C ∧ |C|<meanG (finiteSpectrum w q hw) a := by
  exact nesterov.Spread.exists_finite_halfstep a D.negative_t D.period_ge hs hs1
    D.eta_pos D.eta_lt_one D.defect_nonneg D.defect_le_margin D.small
    D.R D.Θ D.radius_pos D.polar D.defect D.first_lag

end Spread.PreparedBand

theorem rest_witness_of_finite_feasible {J : Type} [Fintype J]
    (q : Momentum.Tuning) {μ L r C : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (hr : 0<r)
    (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hfeas : Feasible ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair
      μ L (Real.log r)) (Real.log r) (finiteSpectrum w c hw) C)
    (hreserve : |C|<meanG (finiteSpectrum w c hw)
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r))) :
    RestLowerWitness q μ L r (2*Fintype.card J+1) := by
  obtain ⟨lam,hlam,Y,f,hY,hf,hlim,hx,heq,c₀,hc₀,hbound⟩ :=
    Realization.exists_real_startup q hμ hμL hs w c hw hfeas (fun _=>hreserve)
  let x₀ := Realization.startupCoordinates J
    (Realization.physical (finiteLatent w c (Real.log r)) q.beta q.tau q.stepSize lam Y 0)
  refine ⟨f,x₀,hf,hx,c₀,hc₀,fun N=>?_⟩
  have hex : Real.exp ((N:ℝ)*Real.log r)=r^N := by
    rw [Real.exp_nat_mul,Real.exp_log hr]
  simpa only [hex] using hbound N

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem spread_witness {c s lam : ℝ} {K : A→ℕ} {M X : A→ℝ}
    (hc0 : 0<c) (hc : c<θ/2) (hτ : 0<τ)
    (hs0 : 0<s) (hs1 : s≤nesterov.Spread.canonicalKernel.s1) (hlam : 0<lam)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hK : ∀ᶠ a in l,3≤K a)
    (hM : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      |mixedPolynomial (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-c*F.epsilon a) (1-Real.cos ω)|≤M a)
    (hX : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ‖Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω‖≤X a)
    (hH : ∀ᶠ a in l,∀ ω∈Spread.band s (nesterov.Spread.centerAngle (K a)),
      ((1-circle (1-c*F.epsilon a) ω)*
        Spread.product (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) ω).re≤
          -lam*F.epsilon a*X a)
    (hεscale : Tendsto (fun a=>F.epsilon a/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0))
    (hMscale : Tendsto (fun a=>M a/Spread.cubicScale
      (Spread.xiMax s (nesterov.Spread.centerAngle (K a)))) l (𝓝 0)) :
    ∀ᶠ a in l,∃ (J : Type) (_ : Fintype J) (w : J→ℝ≥0) (q : J→Frequency)
      (hw : ∑ j,w j=1),
      (∀ j,Real.arccos (q j:ℝ)∈Spread.sourceBand (K a) s) ∧
      ∃ C : ℝ,Feasible (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a))
        (Real.log (1-c*F.epsilon a)) (finiteSpectrum w q hw) C ∧
      |C|<meanG (finiteSpectrum w q hw)
        (Spread.pair (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a)) ∧
      RestLowerWitness (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) (2*Fintype.card J+1) ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  obtain ⟨η,hη,hη1,hprep⟩ := F.prepare_spread_band hc0 hc hτ hs0 hs1 hlam
    hK hM hX hH hεscale hMscale
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [hprep,hstable,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with a hp hs he he1 hr
  obtain ⟨D⟩ := hp
  obtain ⟨J,inst,w,q,hw,hband,C,hfeas,hreserve⟩ := D.finite hs0 hs1
  let : Fintype J := inst
  have hμ : 0<F.epsilon a^2 := sq_pos_of_pos he
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hwitness := rest_witness_of_finite_feasible (F.tuning a) hμ hμL hs hr w q hw hfeas hreserve
  have hrate := Realization.exp_le_momentumRestRate_of_feasible (F.tuning a) hμ hμL hs
    w q hw hfeas (fun _=>hreserve)
  rw [Real.exp_log hr] at hrate
  exact ⟨J,inst,w,q,hw,hband,C,hfeas,hreserve,hwitness,hrate⟩

end Scaling
end
end nesterov.TwoStep

import nesterov.TwoStep.SequenceCeiling
import nesterov.TwoStep.Lower
import nesterov.TwoStep.Wall
import nesterov.TwoStep.FrontierPrice

/-! Sequence ceilings and the half-step necessity, without assuming that the
original physical parameters converge. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology
namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem stability_margin_le [NeBot l]
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) : y*(1+2*τ)≤4 := by
  have hm := F.step_tendsto.mul ((tendsto_const_nhds (x:=(1:ℝ))).add (F.tau_tendsto.const_mul 2))
  apply le_of_tendsto hm
  filter_upwards [hstable,F.epsilon_pos,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with a hs he he1
  have hh := ((F.tuning a).stable_iff (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)).mp hs
  simp only [mul_one] at hh
  nlinarith [(F.tuning a).beta_lt_one]

end Scaling
namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℕ atTop θ y τ)

/-- The sampled-flow ceiling along every sequence, obtained from a proved real
extension rather than any regularity assumed on the physical parameters. -/
theorem sequence_rest_coefficient_eventually_lt
    (hstable : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1)
    {b : ℝ} (hb : Flow.cF θ y<b) : ∀ᶠ n in atTop,F.restCoefficientAt n<b := by
  obtain ⟨d,hd,hdb⟩ := exists_between hb
  exact (F.rest_coefficient_eventually_le_filter hstable hd).mono fun _ ha=>ha.trans_lt hdb

/-- Every accelerated full-class sequence has limiting extrapolation at least one half. -/
theorem half_le_tau_of_full_acceleration {c : ℝ} (hc : 0<c)
    (hstable : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1)
    (hfull : ∀ᶠ n in atTop,Momentum.momentumRate (F.tuning n).beta (F.tuning n).tau
      (F.tuning n).stepSize (F.tuning n).step_pos.ne' (F.epsilon n^2) 1≤1-c*F.epsilon n) :
    1/2≤τ := by
  by_contra hh
  obtain ⟨T,hτT,hT⟩ := exists_between (lt_of_not_ge hh)
  have hquad : ∀ᶠ n in atTop,Quadratic.quadraticRate (F.epsilon n^2) 1 (F.tuning n).beta
      (F.tuning n).tau (F.tuning n).stepSize≤1-c*F.epsilon n := by
    filter_upwards [hfull,F.epsilon_pos,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn he he1
    exact (Momentum.quadraticRate_le_momentumRate (β:=(F.tuning n).beta) (τ:=(F.tuning n).tau)
      (F.tuning n).step_pos.ne' (sq_pos_of_pos he) (by nlinarith : F.epsilon n^2<1)).trans hn
  have ht : ∀ᶠ n in atTop,(F.tuning n).tau≤T :=
    (F.tau_tendsto.eventually (eventually_lt_nhds hτT)).mono fun _ h=>h.le
  have hw := wall_restRate hc F.epsilon_tendsto hstable hquad hT ht
  have hsmall := F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨n,hn,hfulln,he,he1⟩ := (hw.and (hfull.and (F.epsilon_pos.and hsmall))).exists
  have hr := Momentum.restRate_le_momentumRate (β:=(F.tuning n).beta) (τ:=(F.tuning n).tau)
    (F.tuning n).step_pos.ne' (sq_pos_of_pos he) (by nlinarith : F.epsilon n^2<1)
  have hrate := hr.trans hfulln
  nlinarith [mul_pos hc he]

end Scaling
end
end nesterov.TwoStep

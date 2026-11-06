import nesterov.Slow.Sampled
import nesterov.Slow.Roots
import nesterov.Spectral.Rotation
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
Article: Theorem 5.2. The true uniform rate of every continuous finite-memory
second-order family is bounded below by the sampled flow witnesses.
-/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Filter Flow Set Spectral
open scoped Topology

theorem exponential_coefficient_limit (c : ℝ) :
    Tendsto (fun ε : ℝ=>(1-Real.exp (-c*ε))/ε) (𝓝[>] (0:ℝ)) (𝓝 c) := by
  let f := fun ε : ℝ=>Real.exp (-c*ε)
  have hd : HasDerivAt f (-c) 0 := by
    simpa only [mul_zero,Real.exp_zero,one_mul,mul_one] using (((hasDerivAt_id' (0:ℝ)).const_mul (-c)).exp)
  have hh : Tendsto (fun ε : ℝ=> -dslope f 0 ε) (𝓝[>] (0:ℝ)) (𝓝 (-dslope f 0 0)) :=
    (continuousAt_dslope_same.mpr hd.differentiableAt).tendsto.neg.mono_left nhdsWithin_le_nhds
  have hv : -(dslope f 0 0)=c := by rw [dslope_same,hd.deriv];ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dslope_of_ne f hε.ne']
  simp only [slope_def_field,sub_zero,f,mul_zero,Real.exp_zero]
  ring

variable {θ y : ℝ} (F : SecondOrderFamily θ y)

def coefficient (ε : ℝ) : ℝ := (1-Rates.rate (F.method ε) (ε^2) 1)/ε

theorem sampled_rate_lower {c : ℝ} (hc : θ/3<c) (hcQ : c<cQ θ y) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),Real.exp (-c*ε)≤Rates.rate (F.method ε) (ε^2) 1 := by
  obtain ⟨W⟩ := exists_spread F.theta_pos F.step_pos hc hcQ
  have hcp : 0<c := by linarith [F.theta_pos]
  have hb : 0≤θ-2*c := by linarith [(lt_cQ_iff θ y c).mp hcQ |>.1]
  have hw := sampled_flow_feasible F W hcp hb
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hw,hsmall,self_mem_nhdsWithin] with ε hε hε1 hε0
  obtain ⟨v,hv,C,hf,_,_⟩ := hε
  have he : 0<ε := hε0
  have hμL : ε^2<1 := by nlinarith
  exact hf.exp_le_rate (sq_pos_of_pos he) hμL

/-- Every strict test level above c_F eventually bounds the actual coefficient.
This formulation also covers families with unstable independent fast modes. -/
theorem coefficient_eventually_le {a : ℝ} (ha : cF θ y<a) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),F.coefficient ε≤a := by
  by_cases hQ : cQ θ y≤θ/3
  · have hca : cQ θ y<a := by simpa only [cF,min_eq_right hQ] using ha
    have hquad := F.quadratic_coefficient_eventually_le hca
    have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hquad,hsmall,self_mem_nhdsWithin] with ε he hε1 hε0
    have hε : 0<ε := hε0
    have hμL : ε^2<1 := by nlinarith
    have hbound := Rates.quadraticRate_le_rate (F.method ε) (sq_pos_of_pos hε) hμL
    exact (div_le_div_of_nonneg_right (by linarith : 1-Rates.rate (F.method ε) (ε^2) 1≤
      1-Rates.quadraticRate (F.method ε) (ε^2) 1) hε.le).trans he
  · have hgap : θ/3<cQ θ y := lt_of_not_ge hQ
    have hta : θ/3<a := by simpa only [cF,min_eq_left hgap.le] using ha
    obtain ⟨c,hc,hcmin⟩ := exists_between (lt_min hta hgap)
    have hca : c<a := hcmin.trans_le (min_le_left _ _)
    have hcQ : c<cQ θ y := hcmin.trans_le (min_le_right _ _)
    have hr := F.sampled_rate_lower hc hcQ
    have hl := (exponential_coefficient_limit c).eventually (eventually_lt_nhds hca)
    filter_upwards [hr,hl,self_mem_nhdsWithin] with ε hrate hexp hε
    have hpos : 0<ε := hε
    have he := div_le_div_of_nonneg_right (show 1-Rates.rate (F.method ε) (ε^2) 1≤1-Real.exp (-c*ε) by linarith) hpos.le
    exact he.trans hexp.le

/-- The source limsup, in extended reals to retain arbitrarily unstable families. -/
theorem limsup_coefficient_le :
    limsup (fun ε=>(F.coefficient ε:EReal)) (𝓝[>] (0:ℝ))≤(cF θ y:EReal) := by
  by_contra h
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hreal : cF θ y<a := EReal.coe_lt_coe_iff.mp ha
  have he : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.coefficient ε:EReal)≤(a:EReal) := by
    filter_upwards [F.coefficient_eventually_le hreal] with ε hε
    exact EReal.coe_le_coe_iff.mpr hε
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) he)) halim

end
end nesterov.Slow.SecondOrderFamily

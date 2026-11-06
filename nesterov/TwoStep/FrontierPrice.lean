import nesterov.TwoStep.AsymptoticsModel
import nesterov.Quadratic.Price
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Article: Corollary `cor:frontier` (i). The price ceiling covers arbitrary
physical parameter families, including unstable ones and nonconvergent β,h. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def fixedExtrapolationCeiling (τ : ℝ) : ℝ := 2/Real.sqrt (1+2*τ)
def finitePriceCeiling (ε τ : ℝ) : ℝ := 2/(Real.sqrt (1+2*τ-2*τ*ε^2)+ε)

theorem quadratic_price_coefficient (q : Momentum.Tuning) {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) :
    (1-Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize)/ε≤finitePriceCeiling ε q.tau := by
  have hμ : 0<ε^2 := sq_pos_of_pos hε
  have hμL : ε^2<1 := by nlinarith
  have hA : 0<1+2*q.tau-2*q.tau*ε^2 := by
    have hh := mul_nonneg (show 0≤2*q.tau by linarith [q.tau_nonneg]) (sub_pos.mpr hμL).le
    nlinarith
  by_cases hr : Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize<1
  · have hs : q.Stable (ε^2) 1 := (Quadratic.stable_iff_quadraticRate_lt_one hμL.le).mpr hr
    let K := Quadratic.effectiveCondition (ε^2) 1 q.tau
    have hK : 0<K := lt_trans zero_lt_one (Quadratic.effectiveCondition_gt_one hμ hμL q.tau_nonneg)
    have hscale : Real.sqrt K*ε=Real.sqrt (1+2*q.tau-2*q.tau*ε^2) := by
      apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg K) hε.le) (Real.sqrt_nonneg _)).mp
      rw [mul_pow,Real.sq_sqrt hK.le,Real.sq_sqrt hA.le]
      dsimp [K,Quadratic.effectiveCondition]
      field_simp
    have hd : 0<Real.sqrt K+1 := by positivity
    have hp := Quadratic.price_of_extrapolation hμ hμL q.tau_nonneg hs
    have hgap : 1-Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize≤2/(Real.sqrt K+1) := by
      have hh := sub_le_sub_left hp 1
      have hid : 1-Quadratic.priceFactor (ε^2) 1 q.tau=2/(Real.sqrt K+1) := by
        unfold Quadratic.priceFactor
        change 1-(Real.sqrt K-1)/(Real.sqrt K+1)=_
        field_simp
        ring
      rwa [hid] at hh
    calc
      _≤(2/(Real.sqrt K+1))/ε := div_le_div_of_nonneg_right hgap hε.le
      _=finitePriceCeiling ε q.tau := by
        rw [div_div]
        unfold finitePriceCeiling
        congr 1
        nlinarith only [hscale]
  · exact (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le).trans (by
      unfold finitePriceCeiling
      positivity)

theorem finitePriceCeiling_tendsto {A : Type*} {l : Filter A} {ε τ : A→ℝ} {τ₀ : ℝ}
    (he : Tendsto ε l (𝓝 0)) (ht : Tendsto τ l (𝓝 τ₀)) (hτ₀ : 0≤τ₀) :
    Tendsto (fun a=>finitePriceCeiling (ε a) (τ a)) l (𝓝 (fixedExtrapolationCeiling τ₀)) := by
  have hA := (((tendsto_const_nhds (x:=(1:ℝ))).add (ht.const_mul 2)).sub
    ((ht.const_mul 2).mul (he.pow 2))).sqrt
  have hden := hA.add he
  have hden0 : 0<Real.sqrt (1+2*τ₀) := Real.sqrt_pos.mpr (by linarith)
  have hh := (tendsto_const_nhds (x:=(2:ℝ))).div hden
    (by simpa using hden0.ne')
  convert hh using 1
  · funext a
    rfl
  · simp [fixedExtrapolationCeiling]

/-- The quantified sharp ceiling, before any boundedness convention for limsup. -/
theorem fixed_tau_quadratic_eventually_lt {A : Type*} {l : Filter A} [NeBot l]
    {ε : A→ℝ} {q : A→Momentum.Tuning} {τ₀ a : ℝ}
    (he : Tendsto ε l (𝓝[>] (0:ℝ))) (ht : Tendsto (fun n=>(q n).tau) l (𝓝 τ₀))
    (ha : fixedExtrapolationCeiling τ₀<a) :
    ∀ᶠ n in l,(1-Quadratic.quadraticRate (ε n^2) 1 (q n).beta (q n).tau (q n).stepSize)/ε n<a := by
  have hτ₀ : 0≤τ₀ := ge_of_tendsto ht (Eventually.of_forall fun n=>(q n).tau_nonneg)
  have hz := he.mono_right nhdsWithin_le_nhds
  filter_upwards [he.eventually self_mem_nhdsWithin,hz.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    (finitePriceCeiling_tendsto hz ht hτ₀).eventually (eventually_lt_nhds ha)] with n hn hn1 hprice
  exact (quadratic_price_coefficient (q n) hn hn1).trans_lt hprice

/-- Corollary frontier(i), retaining arbitrarily unstable families through EReal. -/
theorem fixed_tau_quadratic_limsup {A : Type*} {l : Filter A} [NeBot l]
    {ε : A→ℝ} {q : A→Momentum.Tuning} {τ₀ : ℝ}
    (he : Tendsto ε l (𝓝[>] (0:ℝ))) (ht : Tendsto (fun n=>(q n).tau) l (𝓝 τ₀)) :
    limsup (fun n=>((1-Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize)/ε n:EReal)) l≤(fixedExtrapolationCeiling τ₀:EReal) := by
  by_contra hh
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  have hbound : ∀ᶠ n in l,((1-Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize)/ε n:EReal)≤(a:EReal) := by
    filter_upwards [fixed_tau_quadratic_eventually_lt he ht (EReal.coe_lt_coe_iff.mp ha)] with n hn
    exact EReal.coe_le_coe_iff.mpr hn.le
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hbound)) halim

end
end nesterov.TwoStep

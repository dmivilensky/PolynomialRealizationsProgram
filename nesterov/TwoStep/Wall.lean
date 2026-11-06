import nesterov.TwoStep.AsymptoticsCompact
import nesterov.TwoStep.Band

/-! Theorem wall: accelerated tunings uniformly below one half have resonances. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem Ltau_tendsto {A : Type*} {l : Filter A} {β τ yμ y : A→ℝ}
    {β₀ τ₀ yμ₀ y₀ ξ : ℝ} (hβ : Tendsto β l (𝓝 β₀)) (hτ : Tendsto τ l (𝓝 τ₀))
    (hμ : Tendsto yμ l (𝓝 yμ₀)) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun a=>Ltau (β a) (τ a) (yμ a) (y a) ξ) l (𝓝 (Ltau β₀ τ₀ yμ₀ y₀ ξ)) := by
  have hc : Continuous (fun p : ℝ × (ℝ × (ℝ × ℝ))=>Ltau p.1 p.2.1 p.2.2.1 p.2.2.2 ξ) := by
    unfold Ltau A0 A1 A2
    fun_prop
  convert (hc.tendsto (β₀,τ₀,yμ₀,y₀)).comp
    (hβ.prodMk_nhds (hτ.prodMk_nhds (hμ.prodMk_nhds hy))) using 1
  funext a
  rfl

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem exists_wall_period (hτ : τ<1/2) :
    ∃ K : ℕ,6≤K ∧ ∀ᶠ a in l,
      Ltau (F.tuning a).beta (F.tuning a).tau
        ((F.tuning a).stepSize*F.epsilon a^2) (F.tuning a).stepSize
        (1-Real.cos (2*Real.pi/K))<0 := by
  have hw : Tendsto (fun K : ℕ=>2*Real.pi/K) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hξ : Tendsto (fun K : ℕ=>1-Real.cos (2*Real.pi/K)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.cos_zero,sub_self] using (tendsto_const_nhds (x:=(1:ℝ))).sub
      ((Real.continuous_cos.tendsto 0).comp hw)
  have hb : Tendsto (fun K : ℕ=>2*y*(2*τ-1)+4*(1-τ*y)*(1-Real.cos (2*Real.pi/K)))
      atTop (𝓝 (2*y*(2*τ-1))) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_nhds (x:=2*y*(2*τ-1))).add (hξ.const_mul (4*(1-τ*y)))
  have hneg : 2*y*(2*τ-1)<0 := mul_neg_of_pos_of_neg (mul_pos (by norm_num) F.step_pos) (by linarith)
  obtain ⟨K,hK,hbK⟩ := ((eventually_ge_atTop 6).and
    (hb.eventually (eventually_lt_nhds hneg))).exists
  have hangle : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
    simpa [polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hξpos : 0<1-Real.cos (2*Real.pi/K) := sub_pos.mpr (by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) hangle.2.le hangle.1)
  have hlim : Ltau 1 τ 0 y (1-Real.cos (2*Real.pi/K))<0 := by
    rw [Ltau_limit]
    nlinarith [mul_neg_of_pos_of_neg hξpos hbK]
  have hμ : Tendsto (fun a=>(F.tuning a).stepSize*F.epsilon a^2) l (𝓝 0) := by
    simpa using F.step_tendsto.mul (F.epsilon_zero.pow 2)
  exact ⟨K,hK,(Ltau_tendsto F.beta_tendsto F.tau_tendsto hμ F.step_tendsto).eventually
    (eventually_lt_nhds hlim)⟩

end Scaling

/-- The wall conclusion for arbitrary accelerated parameter sequences, before
any convergence of the tuning parameters has been assumed. -/
theorem wall_negative_polynomial {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c T : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hT : T<1/2) (hτ : ∀ᶠ n in atTop,(q n).tau≤T) :
    ∀ᶠ n in atTop,∃ K : ℕ,6≤K ∧
      Ltau (q n).beta (q n).tau ((q n).stepSize*ε n^2) (q n).stepSize
        (1-Real.cos (2*Real.pi/K))<0 := by
  by_contra hn
  have hbad : ∃ᶠ n in atTop,¬∃ K : ℕ,6≤K ∧
      Ltau (q n).beta (q n).tau ((q n).stepSize*ε n^2) (q n).stepSize
        (1-Real.cos (2*Real.pi/K))<0 := by simpa only [not_eventually] using hn
  obtain ⟨ψ,hψ,hbadψ⟩ := subseq_forall_of_frequently
    (p:=fun n : ℕ=>¬∃ K : ℕ,6≤K ∧
      Ltau (q n).beta (q n).tau ((q n).stepSize*ε n^2) (q n).stepSize
        (1-Real.cos (2*Real.pi/K))<0) tendsto_id hbad
  obtain ⟨φ,hφ,θ,y,τ,hθ,hy,hτ₀,_,F,hFe,hFq⟩ := accelerated_subsequence hc (he.comp hψ)
    (hψ.eventually hstable) (hψ.eventually hrate)
  have htau : τ≤T := by
    apply le_of_tendsto F.tau_tendsto
    filter_upwards [hφ.tendsto_atTop.eventually (hψ.eventually hτ)] with n hn
    simpa only [hFq,Function.comp_def] using hn
  obtain ⟨K,hK,hneg⟩ := F.exists_wall_period (htau.trans_lt hT)
  obtain ⟨n,hn⟩ := hneg.exists
  have hh := hbadψ (φ n)
  apply hh
  refine ⟨K,hK,?_⟩
  simpa only [hFe,hFq,Function.comp_def] using hn

theorem wall_restRate {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c T : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hT : T<1/2) (hτ : ∀ᶠ n in atTop,(q n).tau≤T) :
    ∀ᶠ n in atTop,1<Momentum.momentumRestRate (q n).beta (q n).tau
      (q n).stepSize (q n).step_pos.ne' (ε n^2) 1 := by
  filter_upwards [wall_negative_polynomial hc he hstable hrate hT hτ,hstable,
    he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with n hn hs hn0 hn1
  obtain ⟨K,hK,hneg⟩ := hn
  exact negative_Ltau_restRate (q n) (K:=K) (sq_pos_of_pos hn0) (by nlinarith) hs (by omega)
    (by simpa only [mul_one] using hneg)

theorem wall_periodic_rest {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c T : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hT : T<1/2) (hτ : ∀ᶠ n in atTop,(q n).tau≤T) :
    ∀ᶠ n in atTop,∃ K : ℕ,6≤K ∧ HasPeriodicRestWitness (q n) (ε n^2) 1 K ∧
      1<Momentum.momentumRestRate (q n).beta (q n).tau
        (q n).stepSize (q n).step_pos.ne' (ε n^2) 1 := by
  filter_upwards [wall_negative_polynomial hc he hstable hrate hT hτ,hstable,
    he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with n hn hs hn0 hn1
  obtain ⟨K,hK,hneg⟩ := hn
  have hμ : 0<ε n^2 := sq_pos_of_pos hn0
  have hμL : ε n^2<1 := by nlinarith
  have hneg' : Ltau (q n).beta (q n).tau ((q n).stepSize*ε n^2) ((q n).stepSize*1)
      (1-Real.cos (2*Real.pi/K))<0 := by simpa only [mul_one] using hneg
  exact ⟨K,hK,negative_Ltau_periodic_rest (q n) (K:=K) hμ hμL hs (by omega) hneg',
    negative_Ltau_restRate (q n) (K:=K) hμ hμL hs (by omega) hneg'⟩

/-- The quantified liminf conclusion of the wall theorem. -/
theorem wall_liminf {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hrest : ∀ᶠ n in atTop,Momentum.momentumRestRate (q n).beta (q n).tau
      (q n).stepSize (q n).step_pos.ne' (ε n^2) 1≤1) :
    ∀ δ : ℝ,0<δ → ∀ᶠ n in atTop,1/2-δ≤(q n).tau := by
  intro δ hδ
  by_contra hn
  have hbad : ∃ᶠ n in atTop,(q n).tau<1/2-δ := by simpa only [not_eventually,not_le] using hn
  obtain ⟨ψ,hψ,hbadψ⟩ := subseq_forall_of_frequently (p:=fun n : ℕ=>(q n).tau<1/2-δ)
    tendsto_id hbad
  have hwall := wall_restRate hc (he.comp hψ) (hψ.eventually hstable) (hψ.eventually hrate)
    (T:=1/2-δ) (by linarith) (Eventually.of_forall fun n=>(hbadψ n).le)
  obtain ⟨n,hn,hbound⟩ := (hwall.and (hψ.eventually hrest)).exists
  exact (not_lt_of_ge hbound) hn

private theorem accelerated_tau_bounded {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n) :
    ∀ᶠ n in atTop,(q n).tau≤2/c^2 := by
  filter_upwards [he.eventually self_mem_nhdsWithin,hstable,hrate,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with n hn hs hr hn1
  exact (accelerated_tuning_bounds (q n) hn hn1 hc hs hr).2.2.1.le

/-- The source wall hypothesis stated with the literal limsup. -/
theorem wall_of_limsup {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hlim : limsup (fun n=>(q n).tau) atTop<1/2) :
    ∀ᶠ n in atTop,∃ K : ℕ,6≤K ∧ HasPeriodicRestWitness (q n) (ε n^2) 1 K ∧
      1<Momentum.momentumRestRate (q n).beta (q n).tau
        (q n).stepSize (q n).step_pos.ne' (ε n^2) 1 := by
  obtain ⟨T,hTlim,hT⟩ := exists_between hlim
  have hb : IsBoundedUnder (·≤·) atTop (fun n=>(q n).tau) :=
    ⟨2/c^2,accelerated_tau_bounded hc he hstable hrate⟩
  exact wall_periodic_rest hc he hstable hrate hT
    ((eventually_lt_of_limsup_lt hTlim hb).mono fun _ hn=>hn.le)

/-- The source's necessary half-step rule, with the literal liminf. -/
theorem half_le_liminf_tau {ε : ℕ→ℝ} {q : ℕ→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε atTop (𝓝[>] (0:ℝ)))
    (hstable : ∀ᶠ n in atTop,(q n).Stable (ε n^2) 1)
    (hrate : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize≤1-c*ε n)
    (hrest : ∀ᶠ n in atTop,Momentum.momentumRestRate (q n).beta (q n).tau
      (q n).stepSize (q n).step_pos.ne' (ε n^2) 1≤1) :
    1/2≤liminf (fun n=>(q n).tau) atTop := by
  have hb : IsBoundedUnder (·≥·) atTop (fun n : ℕ=>(q n).tau) := by
    refine ⟨0,?_⟩
    change ∀ᶠ n : ℕ in atTop,0≤(q n).tau
    exact Eventually.of_forall fun n=>(q n).tau_nonneg
  have hco : IsCoboundedUnder (·≥·) atTop (fun n : ℕ=>(q n).tau) :=
    isCoboundedUnder_ge_of_eventually_le atTop (accelerated_tau_bounded hc he hstable hrate)
  apply (le_liminf_iff' hco hb).mpr
  intro a ha
  have ht := wall_liminf hc he hstable hrate hrest (1/2-a) (by linarith)
  filter_upwards [ht] with n hn
  linarith

end
end nesterov.TwoStep

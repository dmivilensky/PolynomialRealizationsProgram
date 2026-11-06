import nesterov.TwoStep.FrontierSequences
import nesterov.Flow.LevelSets

/-! Frontier(v): compactness forces the optimal slow data for every stable
physical family, without assuming convergence of any tuning parameter. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def tuningFullCoefficient (ε : ℝ) (q : Momentum.Tuning) : ℝ :=
  (1-Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' (ε^2) 1)/ε

def parameterTriple (ε : ℝ) (q : Momentum.Tuning) : ℝ×(ℝ×ℝ) :=
  ((1-q.beta)/ε,(q.stepSize,q.tau))

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℕ atTop θ y τ)

/-- Rigidity of every convergent slow-data subsequence at constant at least one. -/
theorem optimal_limit_data
    (hs : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1)
    (hunit : ∀ c : ℝ,c<1 → ∀ᶠ n in atTop,c≤F.fullCoefficientAt n) :
    θ=3 ∧ y=2 ∧ τ=1/2 := by
  have hfull : ∀ᶠ n in atTop,Momentum.momentumRate (F.tuning n).beta (F.tuning n).tau
      (F.tuning n).stepSize (F.tuning n).step_pos.ne' (F.epsilon n^2) 1≤1-(1/2)*F.epsilon n := by
    filter_upwards [hunit (1/2) (by norm_num),F.epsilon_pos] with n hn he
    have hh := (le_div_iff₀ he).mp hn
    change (1/2)*F.epsilon n≤1-Momentum.momentumRate (F.tuning n).beta (F.tuning n).tau
      (F.tuning n).stepSize (F.tuning n).step_pos.ne' (F.epsilon n^2) 1 at hh
    linarith
  have hτ := F.half_le_tau_of_full_acceleration (by norm_num : (0:ℝ)<1/2) hs hfull
  have hm := F.stability_margin_le hs
  have hcf : 1≤Flow.cF θ y := by
    by_contra hh
    obtain ⟨c,hc,hc1⟩ := exists_between (lt_of_not_ge hh)
    obtain ⟨d,hd,hdc⟩ := exists_between hc
    obtain ⟨n,hn,hu⟩ := ((hunit c hc1).and (F.full_coefficient_eventually_le_filter hs hd)).exists
    exact (not_lt_of_ge hn) (hu.trans_lt hdc)
  have hy : 2≤y := by simpa using (Flow.minimum_step_of_level (by norm_num : (0:ℝ)<1) hcf).1
  have hytwo : y=2 := by
    have hp := mul_nonneg F.step_pos.le (sub_nonneg.mpr hτ)
    nlinarith
  have hθy := (Flow.le_cF_iff (by norm_num : (0:ℝ)≤1) θ y).mp hcf
  norm_num at hθy
  exact ⟨by nlinarith [hθy.1,hθy.2],hytwo,by rw [hytwo] at hm;nlinarith⟩

end Scaling

/-- The sequential-compactness conclusion already holds under the quantified
liminf hypothesis; the original tuning parameters need not have limits. -/
theorem optimal_parameters_tendsto_of_lower {A : Type*} {l : Filter A} [NeBot l]
    [l.IsCountablyGenerated] {ε : A→ℝ} {q : A→Momentum.Tuning}
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hs : ∀ᶠ a in l,(q a).Stable (ε a^2) 1)
    (hunit : ∀ c : ℝ,c<1 → ∀ᶠ a in l,c≤tuningFullCoefficient (ε a) (q a)) :
    Tendsto (fun a=>parameterTriple (ε a) (q a)) l (𝓝 (3,(2,1/2))) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  by_contra hh
  have hbad : ∃ᶠ a in l,δ≤dist (parameterTriple (ε a) (q a)) (3,(2,1/2)) := by
    simpa only [not_eventually,not_lt] using hh
  obtain ⟨s,hsl,hbad⟩ := exists_seq_forall_of_frequently hbad
  have heS := he.comp hsl
  have hsS := hsl.eventually hs
  have hfullS : ∀ᶠ n in atTop,Momentum.momentumRate (q (s n)).beta (q (s n)).tau
      (q (s n)).stepSize (q (s n)).step_pos.ne' (ε (s n)^2) 1≤1-(1/2)*ε (s n) := by
    filter_upwards [hsl.eventually (hunit (1/2) (by norm_num)),heS.eventually self_mem_nhdsWithin]
      with n hn he
    dsimp only [Function.comp_def] at he
    have hh := (le_div_iff₀ he).mp hn
    linarith
  have hquadS : ∀ᶠ n in atTop,Quadratic.quadraticRate (ε (s n)^2) 1 (q (s n)).beta
      (q (s n)).tau (q (s n)).stepSize≤1-(1/2)*ε (s n) := by
    filter_upwards [hfullS,heS.eventually self_mem_nhdsWithin,
      (heS.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with n hn he he1
    dsimp only [Function.comp_def] at he he1
    exact (Momentum.quadraticRate_le_momentumRate (β:=(q (s n)).beta) (τ:=(q (s n)).tau)
      (q (s n)).step_pos.ne' (sq_pos_of_pos he) (by nlinarith : ε (s n)^2<1)).trans hn
  obtain ⟨φ,hφ,θ,y,τ,_,_,_,_,F,hFe,hFq⟩ :=
    accelerated_subsequence (by norm_num : (0:ℝ)<1/2) heS hsS hquadS
  have hFs : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1 := by
    simpa only [hFe,hFq,Function.comp_def] using hφ.tendsto_atTop.eventually hsS
  have hFunit (c : ℝ) (hc : c<1) : ∀ᶠ n in atTop,c≤F.fullCoefficientAt n := by
    simpa only [Scaling.fullCoefficientAt,hFe,hFq,Function.comp_def,tuningFullCoefficient] using
      hφ.tendsto_atTop.eventually (hsl.eventually (hunit c hc))
  obtain ⟨hθ,hy,hτ⟩ := F.optimal_limit_data hFs hFunit
  have ht := F.theta_tendsto.prodMk_nhds (F.step_tendsto.prodMk_nhds F.tau_tendsto)
  have htarget : (θ,(y,τ))=(3,(2,1/2)) := by rw [hθ,hy,hτ]
  rw [htarget] at ht
  have ht' : Tendsto (fun n=>parameterTriple (ε (s (φ n))) (q (s (φ n)))) atTop (𝓝 (3,(2,1/2))) := by
    simpa only [parameterTriple,hFe,hFq,Function.comp_def] using ht
  have hd : Tendsto (fun n=>dist (parameterTriple (ε (s (φ n))) (q (s (φ n))))
      (3,(2,1/2))) atTop (𝓝 0) := by
    simpa only [dist_self] using ht'.dist (tendsto_const_nhds (x:=((3,(2,1/2)):ℝ×(ℝ×ℝ))))
  obtain ⟨n,hn⟩ := (hd.eventually (eventually_lt_nhds hδ)).exists
  have hb := hbad (φ n)
  exact (not_lt_of_ge hb) (by simpa only [dist_self] using hn)

/-- Corollary frontier(v), with the source's literal extended-real liminf. -/
theorem optimal_parameters_tendsto {A : Type*} {l : Filter A} [NeBot l]
    [l.IsCountablyGenerated] {ε : A→ℝ} {q : A→Momentum.Tuning}
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hs : ∀ᶠ a in l,(q a).Stable (ε a^2) 1)
    (hlim : (1:EReal)≤liminf (fun a=>(tuningFullCoefficient (ε a) (q a):EReal)) l) :
    Tendsto (fun a=>parameterTriple (ε a) (q a)) l (𝓝 (3,(2,1/2))) := by
  apply optimal_parameters_tendsto_of_lower he hs
  intro c hc
  have hh : (c:EReal)<liminf (fun a=>(tuningFullCoefficient (ε a) (q a):EReal)) l :=
    (EReal.coe_lt_coe_iff.mpr hc).trans_le hlim
  exact (Filter.eventually_lt_of_lt_liminf hh).mono fun _ ha=>(EReal.coe_lt_coe_iff.mp ha).le

end
end nesterov.TwoStep

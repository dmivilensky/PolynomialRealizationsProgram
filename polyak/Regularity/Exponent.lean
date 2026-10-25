import polyak.Spectral.ActualBoundary
import polyak.Spiral.Regularity
import Mathlib.Topology.Semicontinuity.Basic

/-!
Article: Theorem spectral and Appendix C, regularity of the actual maximal exponent.
Use: logarithmic tuning removes the singular coordinate log q from the compact
feasibility graph. These conclusions concern the attained maximum T itself.
-/

namespace polyak.Regularity
noncomputable section
open Set Filter Spectral
open scoped Topology

/-- Article: the actual exponent as a function of the logarithmic tuning parameter. -/
def logarithmicExponent (a : ℝ) : ℝ := T (Real.exp a)

/-- Article: the maximal actual exponent is upper semicontinuous.
Proof: project a bounded closed set of genuinely feasible data, including its measure. -/
theorem logarithmicExponent_upperSemicontinuousAt (a : ℝ) :
    UpperSemicontinuousAt logarithmicExponent a := by
  rw [upperSemicontinuousAt_iff]
  intro b hb
  let J := Icc (a-1) (a+1)
  let I := Icc (a-1-Real.arsinh 1) (a+1+Real.arsinh 1)
  let S : Set ((ℝ×ℝ)×(Spectrum×ℝ)) :=
    {p | p.1.1∈J ∧ p.1.2∈I ∧ b≤p.1.2 ∧
      Feasible (p.1.2-p.1.1) p.1.2 p.2.1 p.2.2}
  have hclosed : IsClosed S := by
    exact (isClosed_Icc.preimage continuous_fst.fst).inter
      ((isClosed_Icc.preimage continuous_fst.snd).inter
        ((isClosed_le continuous_const continuous_fst.snd).inter
          (isClosed_feasible continuous_snd.fst
            (continuous_fst.snd.sub continuous_fst.fst) continuous_fst.snd continuous_snd.snd)))
  have hcomp : IsCompact S := by
    apply ((isCompact_Icc.prod isCompact_Icc).prod
      (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))).of_isClosed_subset hclosed
    intro p hp
    exact ⟨⟨hp.1,hp.2.1⟩,mem_univ _,abs_le.mp hp.2.2.2.abs_C_le_one⟩
  have hbad : IsClosed ((fun p : (ℝ×ℝ)×(Spectrum×ℝ) => p.1.1) '' S) :=
    (hcomp.image continuous_fst.fst).isClosed
  have ha : a∉(fun p : (ℝ×ℝ)×(Spectrum×ℝ) => p.1.1) '' S := by
    rintro ⟨⟨⟨a',t⟩,ν,C⟩,hp,he⟩
    dsimp at he
    subst a'
    have hfeas : t∈exponents (Real.exp a) := by
      refine ⟨ν,C,?_⟩
      simpa only [Real.log_exp] using hp.2.2.2
    have := (isGreatest_T (Real.exp_pos a)).2 hfeas
    change t≤logarithmicExponent a at this
    linarith [hp.2.2.1]
  have hgood := hbad.isOpen_compl.mem_nhds ha
  have hnear : ∀ᶠ a' in 𝓝 a, a'∈J := Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hgood,hnear] with a' hgood ha'
  by_contra hn
  have hb' : b≤logarithmicExponent a' := le_of_not_gt hn
  obtain ⟨ν,C,hfeas⟩ := T_mem (Real.exp_pos a')
  have hbound := abs_T_sub_log_le (Real.exp_pos a')
  rw [Real.log_exp] at hbound hfeas
  have htI : logarithmicExponent a'∈I := by
    have hh := abs_le.mp hbound
    change a-1≤a' ∧ a'≤a+1 at ha'
    change a-1-Real.arsinh 1≤T (Real.exp a') ∧ T (Real.exp a')≤a+1+Real.arsinh 1
    constructor <;> linarith
  exact hgood ⟨((a',logarithmicExponent a'),(ν,C)),⟨ha',htI,hb',hfeas⟩,rfl⟩

/-- Article: strict increase of the actual exponent for every nondegenerate Polyak tuning.
Proof: strict twist shrink gives a locally feasible larger exponent at the larger q. -/
theorem T_strictMonoOn : StrictMonoOn T (Ioo 0 1) := by
  intro q₁ hq₁ q₂ hq₂ hq
  have hl := Real.log_lt_log hq₁.1 hq
  by_cases ht : T q₁=0
  · have hcrit := (T_eq_zero_iff hq₁.1 hq₁.2).mp ht
    have hsp : Real.log (Spiral.factor q₂)≤T q₂ :=
      (isGreatest_T hq₂.1).2 ⟨_,_,Spiral.actual_feasible hq₂.1 hq₂.2⟩
    rw [ht]
    exact (Real.log_pos (Spiral.one_lt_factor hq₂.1 hq₂.2 (by rwa [← hcrit]))).trans_le hsp
  by_cases hv : T q₁≤Real.log q₂
  · exact hv.trans_lt (log_lt_T hq₂.1 hq₂.2)
  obtain ⟨ν,C,hfeas⟩ := T_mem hq₁.1
  obtain ⟨C',hlocal⟩ := hfeas.interior_mono ht
    (show 0≤T q₁-Real.log q₂ by linarith) (show T q₁-Real.log q₂<T q₁-Real.log q₁ by linarith)
  have hp : Tendsto (fun t : ℝ => (t-Real.log q₂,t)) (𝓝 (T q₁))
      (𝓝 (T q₁-Real.log q₂,T q₁)) :=
    (continuousAt_id.sub continuousAt_const).prodMk_nhds continuousAt_id
  have he := hp.eventually hlocal
  have he' : ∀ᶠ t in 𝓝[>] (T q₁), Feasible (t-Real.log q₂) t ν C' :=
    he.filter_mono nhdsWithin_le_nhds
  obtain ⟨s,hs,hgt⟩ := (he'.and self_mem_nhdsWithin).exists
  exact hgt.trans_le ((isGreatest_T hq₂.1).2 ⟨ν,C',hs⟩)

/-- Article: the critical exponent in logarithmic coordinates is exactly zero. -/
theorem logarithmicExponent_critical :
    logarithmicExponent (Real.log Threshold.criticalQ)=0 := by
  rw [logarithmicExponent,Real.exp_log Threshold.criticalQ_pos]
  exact (T_eq_zero_iff Threshold.criticalQ_pos Threshold.criticalQ_lt_one).mpr rfl

/-- Article: continuity at the critical tuning follows from compactness and the explicit spiral,
without assuming the global boundary classification. -/
theorem logarithmicExponent_continuousAt_critical :
    ContinuousAt logarithmicExponent (Real.log Threshold.criticalQ) := by
  let a := Real.log Threshold.criticalQ
  have hzero : logarithmicExponent a=0 := logarithmicExponent_critical
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hfac := Spiral.factor_analyticAt Threshold.criticalQ_pos Threshold.criticalQ_lt_one
    have hlog : ContinuousAt (fun a' : ℝ => Real.log (Spiral.factor (Real.exp a'))) a := by
      apply ContinuousAt.log
      · apply hfac.continuousAt.comp_of_eq Real.continuous_exp.continuousAt
        exact Real.exp_log Threshold.criticalQ_pos
      · rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos,
          Spiral.factor_critical]
        norm_num
    have hbase : Real.log (Spiral.factor (Real.exp a))=0 := by
      rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos,
        Spiral.factor_critical,Real.log_one]
    have hb0 : b<0 := by rwa [hzero] at hb
    have hlo := hlog.tendsto.eventually (lt_mem_nhds (by rwa [hbase]))
    have hdom : ∀ᶠ a' in 𝓝 a, Real.exp a'<1 := by
      exact Real.continuous_exp.continuousAt.eventually (gt_mem_nhds
        (by rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos]
            ; exact Threshold.criticalQ_lt_one))
    filter_upwards [hlo,hdom] with a' hlo hdom
    exact hlo.trans_le ((isGreatest_T (Real.exp_pos a')).2
      ⟨_,_,Spiral.actual_feasible (Real.exp_pos a') hdom⟩)
  · intro b hb
    exact (upperSemicontinuousAt_iff.mp (logarithmicExponent_upperSemicontinuousAt a)) b hb

end
end polyak.Regularity

import polyak.Asymptotics.SpiralLimit
import polyak.Asymptotics.SmallQActual
import polyak.Boundary.P1.Results
import polyak.Boundary.SpiralArc
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Real.Sqrt

/-!
Article: Theorem regularity, the actual large-condition-number limit.
Use: the actual positive-exponent optimum cannot enter P₁ by its quantitative
origin reserve. Near q=1 the spiral lower bound places it strictly above G₁;
therefore the actual source is the exact spiral and has its proved quartic limit.
-/
namespace polyak.Asymptotics
noncomputable section
open Set Filter Spectral Boundary
open scoped Topology

/-- Every positive actual exponent has cosh strictly below the outer spiral switch. -/
theorem actual_cosh_lt_GW {q : ℝ} (hq : 0<q) (hq1 : q<1) (hT : 0<T q) :
    Real.cosh (T q)<GW := by
  by_contra hh
  have hG : GW≤Real.cosh (T q) := le_of_not_gt hh
  let z:=1/Real.cosh (T q)
  have hGp:=Real.cosh_pos (T q)
  have hz : z∈Ioc (0 : ℝ) P1.zW :=
    ⟨one_div_pos.mpr hGp,one_div_le_one_div_of_le (by linarith [GW_bounds.1]) hG⟩
  have hzcosh : Real.cosh (T q)=1/z := by simp [z]
  have hp:=P1.continuation_physical hz
  let u:=P1.branchU z (P1.continuation z 0)
  have hu : Real.sinh (T q-Real.log q)=u := by
    rw [Regularity.T_sub_log_eq_V hq hq1,P1.continuation_optimal hz hzcosh,Real.sinh_arsinh]
  have hsin : 0≤Real.sinh (T q) := Real.sinh_nonneg_iff.mpr hT.le
  have hless : Real.sinh (T q)<u := by
    rw [←hu]
    exact Real.sinh_lt_sinh.mpr (by linarith [Real.log_neg hq hq1])
  have hbound : Real.cosh (T q)<3/2 := by
    have hs:=Real.sinh_sq (T q)
    have hu1 : u≤1 := hp.u_le_one
    nlinarith
  have hzlo : (2/3 : ℝ)<z := by
    change (2/3 : ℝ)<1/Real.cosh (T q)
    exact (lt_div_iff₀ hGp).mpr (by linarith)
  have hGlo : (4/3 : ℝ)<Real.cosh (T q) := by linarith [GW_bounds.1]
  have hgap : z/2≤1-(P1.branchAtom z (P1.continuation z 1))^2-u^2 := hp.gap_lower
  have hs:=Real.sinh_sq (T q)
  have hu0 : 0≤u := hp.u_nonneg
  nlinarith [sq_nonneg (P1.branchAtom z (P1.continuation z 1))]

/-- Near q=1 the actual optimum lies on the exact spiral arc and equals its positive root. -/
theorem actualFactor_eventually_eq_spiral :
    SmallQ.actualFactor=ᶠ[𝓝[<] (1 : ℝ)] Spiral.factor := by
  have hfactor : ∀ᶠ q in 𝓝[<] (1 : ℝ),(3/2 : ℝ)<Spiral.factor q :=
    spiral_factor_tendsto_one.eventually (lt_mem_nhds (by linarith [limitingFactor_bounds.1]))
  have hdomain : ∀ᶠ q in 𝓝[<] (1 : ℝ),0<q ∧ q<1 :=
    ((lt_mem_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  filter_upwards [hfactor,hdomain] with q hf hq
  have hlog : 0<Real.log (3/2 : ℝ) := Real.log_pos (by norm_num)
  have ht : Real.log (3/2 : ℝ)<T q :=
    (Real.log_lt_log (by norm_num) hf).trans_le
      ((isGreatest_T hq.1).2 ⟨_,_,Spiral.actual_feasible hq.1 hq.2⟩)
  have hT : 0<T q := hlog.trans ht
  have hbase : Real.cosh (Real.log (3/2 : ℝ))=13/12 := by
    rw [Real.cosh_eq,Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ)<3/2)]
    norm_num
  have hcosh:=Real.cosh_strictMonoOn hlog.le hT.le ht
  rw [hbase] at hcosh
  have hGlo : G1<Real.cosh (T q) := by linarith [G1_bounds.2]
  have hGhi:=actual_cosh_lt_GW hq.1 hq.2 hT
  have hv:=spiral_optimal hGlo.le hGhi.le
  have hrel : Spiral.twist (T q)=Real.sinh (T q-Real.log q) := by
    rw [Regularity.T_sub_log_eq_V hq.1 hq.2,hv,Real.sinh_arsinh]
    rfl
  have hpoly:=(Spiral.actual_relation_iff hq.1 (T q)).mp hrel
  exact (Spiral.existsUnique_spiral_root hq.1 hq.2).unique
    ⟨Real.exp_pos _,hpoly⟩ (Spiral.factor_spec hq.1 hq.2)

/-- The actual exact heavy-ball rate has the stated isolated quartic limit as q↑1. -/
theorem actualFactor_tendsto_one :
    Tendsto SmallQ.actualFactor (𝓝[<] (1 : ℝ)) (𝓝 limitingFactor) :=
  (tendsto_congr' actualFactor_eventually_eq_spiral).mpr spiral_factor_tendsto_one

/-- The original condition-number coordinate tends to q=1 from below. -/
theorem conditionQ_tendsto_one :
    Tendsto Dynamics.conditionQ (atTop : Filter ℝ) (𝓝[<] (1 : ℝ)) := by
  have hd : Tendsto (fun κ : ℝ => Real.sqrt κ+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 Real.tendsto_sqrt_atTop
  have hdiv:=hd.const_div_atTop (2 : ℝ)
  have hlim : Tendsto (fun κ : ℝ => 1-2/(Real.sqrt κ+1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hdiv)
  have heq : Dynamics.conditionQ=(fun κ : ℝ => 1-2/(Real.sqrt κ+1)) := by
    funext κ
    unfold Dynamics.conditionQ
    field_simp
    ring
  have hq : Tendsto Dynamics.conditionQ (atTop : Filter ℝ) (𝓝 1) := by rwa [heq]
  refine tendsto_nhdsWithin_iff.mpr ⟨hq,?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with κ hκ
  exact (Threshold.conditionQ_mem hκ).2

/-- The final large-κ assertion concerns the actual algorithmic rate, with the
independently isolated unique positive root and its exact decimal enclosure. -/
theorem conditionRate_tendsto_atTop :
    Tendsto Regularity.conditionRate (atTop : Filter ℝ) (𝓝 limitingFactor) := by
  exact actualFactor_tendsto_one.comp conditionQ_tendsto_one

end
end polyak.Asymptotics

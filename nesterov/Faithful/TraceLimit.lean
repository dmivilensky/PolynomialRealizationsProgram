import nesterov.Faithful.CoefficientLimits
import nesterov.Faithful.SourcePhase
import nesterov.Trace.Formula

/-! The removable low-frequency value of the literal source trace integrand. -/
namespace nesterov.Faithful
noncomputable section
open Filter Set Polynomial
open scoped Topology

theorem trace_symbol_eq (A : Trace.DoubleRootData) (ω : ℝ) :
    A.symbol ω=limitSymbol A.u A.q ω := by
  unfold Trace.DoubleRootData.symbol
  simp_rw [Trace.DoubleRootData.eval_phi]
  simp only [star_neg,mul_neg,neg_mul,neg_neg]
  change ((1-circle ω)*A.method.characteristic 0 (circle ω)*star (A.method.characteristic 1 (circle ω))).re=_
  rw [mul_assoc,←limitProduct_characteristic A.method A.q A.factor]
  rfl

theorem symbol_quartic_ratio (u q : Polynomial ℝ) {y : ℝ} (hy : 0<y)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    Tendsto (fun ω : ℝ=>limitSymbol u q ω/ω^4) (𝓝[≠] (0:ℝ))
      (𝓝 ((2*effectiveLead u q y-1)/(2*y))) := by
  obtain ⟨R,hR,he⟩ := symbol_expansion u q hy hu hq
  have hω : Tendsto (fun ω : ℝ=>ω) (𝓝[≠] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hh := ((hω.pow 2).mul (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).const_add
    ((2*effectiveLead u q y-1)/(2*y))
  simp only [zero_pow (by decide : 2≠0),zero_mul,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ω hω0
  change ω≠0 at hω0
  rw [he]
  field_simp [hω0]

theorem trace_integrand_limit (A : Trace.DoubleRootData) :
    Tendsto A.traceIntegrand (𝓝[>] (0:ℝ)) (𝓝 (4*(2*A.effectiveLead-1)/A.y)) := by
  have hω : Tendsto (fun ω : ℝ=>ω) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hcos : Tendsto (fun ω : ℝ=>Real.cos ω) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa only [Real.cos_zero,Function.comp_def] using Real.continuous_cos.continuousAt.tendsto.comp hω
  have hs := (symbol_quartic_ratio A.u A.q A.y_pos A.u_one A.q_one).mono_left (nhdsGT_le_nhdsNE (0:ℝ))
  have hξ := one_sub_cos_ratio_limit
  have hp : Tendsto (fun ω : ℝ=>Trace.eval (A.phi 1) (circle ω)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hh : ContinuousAt (fun ω : ℝ=>Trace.eval (A.phi 1) (circle ω)) 0 :=
      ((A.phi 1).map Complex.ofRealHom).continuousAt.comp ((analyticAt_circle 0).continuousAt)
    have hv : Trace.eval (A.phi 1) (circle 0)=1 := by rw [circle_zero,Trace.eval_one,A.phi_one];norm_num
    simpa only [hv] using hh.tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  have hn := Complex.continuous_normSq.continuousAt.tendsto.comp hp
  have hh := ((hcos.const_add 1).mul hs).div ((hξ.pow 2).mul hn) (by norm_num)
  convert! hh.congr' ?_ using 1
  · congr 1
    simp only [Complex.normSq_one]
    change 4*(2*A.effectiveLead-1)/A.y=(1+1)*((2*A.effectiveLead-1)/(2*A.y))/((1/2)^2*1)
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with ω hω0
    change 0<ω at hω0
    unfold Trace.DoubleRootData.traceIntegrand
    rw [trace_symbol_eq]
    change ((1+Real.cos ω)*(limitSymbol A.u A.q ω/ω^4))/
      (((1-Real.cos ω)/ω^2)^2*Complex.normSq (Trace.eval (A.phi 1) (circle ω)))=
      (1+Real.cos ω)*limitSymbol A.u A.q ω/
        ((1-Real.cos ω)^2*Complex.normSq (Trace.eval (A.phi 1) (circle ω)))
    field_simp [hω0.ne']

end
end nesterov.Faithful

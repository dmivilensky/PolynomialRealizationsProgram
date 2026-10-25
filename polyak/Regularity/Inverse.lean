import polyak.Regularity.Critical
import Mathlib.Analysis.Analytic.Linear

/-!
Article: Theorem regularity, analytic inversion of the actual spectral boundary.
Use: no continuity of the maximal exponent is assumed. A genuine local implicit
root is feasible and lies below the actual maximum; upper semicontinuity then
proves its continuity and identifies the actual inverse analytically.
-/
namespace polyak.Regularity
noncomputable section
open Spectral Set Filter
open scoped Topology ContDiff

/-- The actual logarithmic rate is analytic at every nonsingular analytic boundary point. -/
theorem logarithmicExponent_analyticAt_of_boundary {a : ℝ} (ha : Real.exp a<1)
    (hV : AnalyticAt ℝ V (logarithmicExponent a))
    (hd : deriv V (logarithmicExponent a)≠1) : AnalyticAt ℝ logarithmicExponent a := by
  let t:=logarithmicExponent a
  let f : ℝ×ℝ → ℝ := fun p => p.2-V p.2-p.1
  have hf : ContDiffAt ℝ ω f (a,t) := by
    have hv : AnalyticAt ℝ (fun p : ℝ×ℝ => V p.2) (a,t) :=
      AnalyticAt.comp (g:=V) (f:=Prod.snd) hV analyticAt_snd
    exact ((analyticAt_snd.sub hv).sub analyticAt_fst).contDiffAt
  have hn : (ω : ℕ∞ω)≠0 := by simp
  have hpartial : HasDerivAt (fun s => f (a,s)) (1-deriv V t) t :=
    ((hasDerivAt_id t).sub hV.differentiableAt.hasDerivAt).sub_const a
  have hi:=chebyshev2.Calculus.scalar_derivative_invertible
    (hf.differentiableAt (by simp)) hpartial (sub_ne_zero.mpr (Ne.symm hd))
  let g:=hf.implicitFunction hn hi
  have hg : AnalyticAt ℝ g a := (hf.contDiffAt_implicitFunction hn hi).analyticAt
  have hg0 : g a=t := hf.implicitFunction_apply_self hn hi
  have hroot : f (a,t)=0 := by
    have hh:=T_sub_log_eq_V (Real.exp_pos a) ha
    rw [Real.log_exp] at hh
    dsimp only [f,t,logarithmicExponent]
    linarith
  have he : ∀ᶠ b in 𝓝 a,f (b,g b)=0 := by
    simpa only [hroot,g] using hf.eventually_apply_implicitFunction hn hi
  have hcand : ∀ᶠ b in 𝓝 a,g b≤logarithmicExponent b := by
    filter_upwards [he] with b hb
    obtain ⟨ν,C,hfeas⟩:=V_mem (g b)
    have hval : g b-Real.log (Real.exp b)=V (g b) := by
      rw [Real.log_exp]
      dsimp only [f] at hb
      linarith
    exact (isGreatest_T (Real.exp_pos b)).2 ⟨ν,C,by rwa [hval]⟩
  have hc : ContinuousAt logarithmicExponent a := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      have hh:=hg.continuousAt.tendsto.eventually (lt_mem_nhds (by rwa [hg0]))
      filter_upwards [hh,hcand] with c hbc hct
      exact hbc.trans_le hct
    · intro b hb
      exact (upperSemicontinuousAt_iff.mp (logarithmicExponent_upperSemicontinuousAt a)) b hb
  have heactual : ∀ᶠ b in 𝓝 a,f (b,logarithmicExponent b)=f (a,t) := by
    have hdom : ∀ᶠ b in 𝓝 a,Real.exp b<1 :=
      Real.continuous_exp.continuousAt.eventually (gt_mem_nhds ha)
    filter_upwards [hdom] with b hb
    have hh:=T_sub_log_eq_V (Real.exp_pos b) hb
    rw [Real.log_exp] at hh
    rw [hroot]
    dsimp only [f,logarithmicExponent]
    linarith
  have hh:=chebyshev2.Calculus.implicit_contDiffWithinAt (s:=univ) hf hn
    hc.continuousWithinAt (by simpa using heactual) hi
  exact (contDiffWithinAt_univ.mp hh).analyticAt

/-- The actual maximal exponent is analytic in the original q coordinate. -/
theorem T_analyticAt_of_boundary {q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hV : AnalyticAt ℝ V (T q)) (hd : deriv V (T q)≠1) : AnalyticAt ℝ T q := by
  have he : logarithmicExponent (Real.log q)=T q := by
    simp only [logarithmicExponent,Real.exp_log hq]
  have hg : AnalyticAt ℝ logarithmicExponent (Real.log q) := by
    apply logarithmicExponent_analyticAt_of_boundary (by rwa [Real.exp_log hq])
    · rwa [he]
    · rwa [he]
  have hh:=hg.comp (analyticAt_log hq)
  apply hh.congr
  filter_upwards [lt_mem_nhds hq] with r hr
  change T (Real.exp (Real.log r))=T r
  rw [Real.exp_log hr]

/-- The original condition-number rate is analytic wherever its actual boundary is. -/
theorem conditionRate_analyticAt_of_boundary {κ : ℝ} (hκ : 1<κ)
    (hV : AnalyticAt ℝ V (T (Dynamics.conditionQ κ)))
    (hd : deriv V (T (Dynamics.conditionQ κ))≠1) : AnalyticAt ℝ conditionRate κ := by
  have hq:=(Threshold.conditionQ_mem hκ).1
  have hq1:=(Threshold.conditionQ_mem hκ).2
  have hT:=T_analyticAt_of_boundary hq hq1 hV hd
  have hs : AnalyticAt ℝ Real.sqrt κ := (Real.contDiffAt_sqrt (by linarith : κ≠0)).analyticAt
  have hQ : AnalyticAt ℝ Dynamics.conditionQ κ := by
    unfold Dynamics.conditionQ
    fun_prop (disch := positivity)
  have he : AnalyticAt ℝ Real.exp (T (Dynamics.conditionQ κ)) :=
    (Real.contDiff_exp : ContDiff ℝ ω Real.exp).contDiffAt.analyticAt
  exact AnalyticAt.comp (g:=Real.exp) (f:=fun r => T (Dynamics.conditionQ r)) he (hT.comp hQ)

end
end polyak.Regularity

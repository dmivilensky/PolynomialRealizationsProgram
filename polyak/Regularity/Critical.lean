import polyak.Regularity.Exponent
import polyak.Boundary.P5.LocalOptimal
import chebyshev2.Calculus.ImplicitScalar
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: Appendix C, the actual rate is analytic at the critical condition number.
Use: invert the actual equation T−V(T)=log q, including its critical endpoint.
The proof uses the already established analytic central optimum, not a proposed branch.
-/

namespace polyak.Regularity
noncomputable section
open Set Filter Spectral
open scoped Topology ContDiff goldenRatio

/-- Article: the actual boundary equation also holds at the critical exponent. -/
theorem T_sub_log_eq_V {q : ℝ} (hq : 0<q) (hq1 : q<1) :
    T q-Real.log q=V (T q) := by
  by_cases ht : T q=0
  · have hqcrit := (T_eq_zero_iff hq hq1).mp ht
    rw [ht,hqcrit,Threshold.log_criticalQ,Threshold.V_zero]
    ring
  · exact actual_boundary hq ht (actual_twist_pos hq hq1)

/-- Article: evenness and differentiability force V′(0)=0. -/
theorem V_hasDerivAt_zero : HasDerivAt V 0 0 := by
  have hd := Boundary.P5.V_analyticAt_zero.differentiableAt.hasDerivAt
  have hn := (by simpa only [neg_zero] using hd : HasDerivAt V (deriv V 0) (-0)).comp
    0 (hasDerivAt_neg (0 : ℝ))
  have he : (fun x : ℝ => V (-x))=V := funext V_even
  change HasDerivAt (fun x : ℝ => V (-x)) _ _ at hn
  rw [he] at hn
  have hd0 : deriv V 0=0 := by
    have hh := hn.unique hd
    linarith
  rwa [hd0] at hd

/-- Article: the actual maximal exponent is analytic through the threshold. -/
theorem logarithmicExponent_analyticAt_critical :
    AnalyticAt ℝ logarithmicExponent (Real.log Threshold.criticalQ) := by
  let a := Real.log Threshold.criticalQ
  let f : ℝ×ℝ → ℝ := fun p => p.2-V p.2-p.1
  have hf : ContDiffAt ℝ ω f (a,logarithmicExponent a) := by
    rw [logarithmicExponent_critical]
    have hV : ContDiffAt ℝ ω V 0 := Boundary.P5.V_analyticAt_zero.contDiffAt
    have hv : ContDiffAt ℝ ω (fun p : ℝ×ℝ => V p.2) (a,0) :=
      ContDiffAt.comp (g:=V) (f:=Prod.snd) (a,0) hV contDiffAt_snd
    exact (contDiffAt_snd.sub hv).sub contDiffAt_fst
  have hn : (ω : ℕ∞ω)≠0 := by simp
  have hdv : HasDerivAt (fun t => f (a,t)) 1 (logarithmicExponent a) := by
    rw [logarithmicExponent_critical]
    simpa only [f,Pi.sub_apply,id_eq,sub_zero] using
      ((hasDerivAt_id (0 : ℝ)).sub V_hasDerivAt_zero).sub_const a
  have hd := chebyshev2.Calculus.scalar_derivative_invertible
    (hf.differentiableAt (by simp)) hdv (by norm_num : (1 : ℝ)≠0)
  have he : ∀ᶠ a' in 𝓝 a, f (a',logarithmicExponent a')=f (a,logarithmicExponent a) := by
    have hdom : ∀ᶠ a' in 𝓝 a, Real.exp a'<1 :=
      Real.continuous_exp.continuousAt.eventually (gt_mem_nhds (by
        rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos]
        exact Threshold.criticalQ_lt_one))
    have heq {a' : ℝ} (ha' : Real.exp a'<1) : f (a',logarithmicExponent a')=0 := by
      have hh := T_sub_log_eq_V (Real.exp_pos a') ha'
      rw [Real.log_exp] at hh
      dsimp only [f,logarithmicExponent]
      linarith
    filter_upwards [hdom] with a' ha'
    rw [heq ha',heq (by
      rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos]
      exact Threshold.criticalQ_lt_one)]
  have hc := chebyshev2.Calculus.implicit_contDiffWithinAt (s:=univ) hf hn
    logarithmicExponent_continuousAt_critical.continuousWithinAt (by simpa using he) hd
  exact (contDiffWithinAt_univ.mp hc).analyticAt

/-- Article: dT/d(log q)=1 exactly at the threshold. -/
theorem logarithmicExponent_hasDerivAt_critical :
    HasDerivAt logarithmicExponent 1 (Real.log Threshold.criticalQ) := by
  let a := Real.log Threshold.criticalQ
  have hg := logarithmicExponent_analyticAt_critical.differentiableAt.hasDerivAt
  have hv : HasDerivAt (fun x => V (logarithmicExponent x)) 0 a := by
    have hh : HasDerivAt V 0 (logarithmicExponent a) := by
      change HasDerivAt V 0 (logarithmicExponent (Real.log Threshold.criticalQ))
      rw [logarithmicExponent_critical]
      exact V_hasDerivAt_zero
    simpa only [Function.comp_def,zero_mul] using hh.comp a hg
  have he : (fun x => logarithmicExponent x-V (logarithmicExponent x))=ᶠ[𝓝 a] id := by
    have hdom : ∀ᶠ a' in 𝓝 a, Real.exp a'<1 :=
      Real.continuous_exp.continuousAt.eventually (gt_mem_nhds (by
        rw [show Real.exp a=Threshold.criticalQ by exact Real.exp_log Threshold.criticalQ_pos]
        exact Threshold.criticalQ_lt_one))
    filter_upwards [hdom] with a' ha'
    have hh := T_sub_log_eq_V (Real.exp_pos a') ha'
    rw [Real.log_exp] at hh
    dsimp [logarithmicExponent]
    linarith
  have hd := (hg.sub hv).congr_of_eventuallyEq he.symm
  have hval : deriv logarithmicExponent a=1 := by
    have hh := hd.unique (hasDerivAt_id a)
    simpa only [sub_zero] using hh
  rwa [hval] at hg

/-- Article: the exact rate as a function of the original condition number. -/
def conditionRate (κ : ℝ) : ℝ := Real.exp (T (Dynamics.conditionQ κ))

/-- Article: the original quadratic tuning parameter increases strictly with κ. -/
theorem conditionQ_strictMonoOn : StrictMonoOn Dynamics.conditionQ (Ioi 1) := by
  intro κ₁ hκ₁ κ₂ hκ₂ hκ
  change 1<κ₁ at hκ₁
  have hs := Real.sqrt_lt_sqrt (by linarith : (0 : ℝ)≤κ₁) hκ
  have hd₁ : 0<Real.sqrt κ₁+1 := by positivity
  have hd₂ : 0<Real.sqrt κ₂+1 := by positivity
  rw [Dynamics.conditionQ,Dynamics.conditionQ,div_lt_div_iff₀ hd₁ hd₂]
  nlinarith

/-- Article: the actual heavy-ball rate increases strictly over the whole physical domain. -/
theorem conditionRate_strictMonoOn : StrictMonoOn conditionRate (Ioi 1) := by
  intro κ₁ hκ₁ κ₂ hκ₂ hκ
  apply Real.exp_lt_exp.mpr
  exact T_strictMonoOn (Threshold.conditionQ_mem hκ₁) (Threshold.conditionQ_mem hκ₂)
    (conditionQ_strictMonoOn hκ₁ hκ₂ hκ)

/-- Article: the condition-number parameterization is an ordinary analytic function at κc. -/
theorem log_conditionQ_analyticAt_critical :
    AnalyticAt ℝ (fun κ => Real.log (Dynamics.conditionQ κ)) Threshold.criticalKappa := by
  have hk : Threshold.criticalKappa≠0 := by linarith [Threshold.one_lt_criticalKappa]
  have hs : AnalyticAt ℝ Real.sqrt Threshold.criticalKappa := (Real.contDiffAt_sqrt hk).analyticAt
  have hden : Real.sqrt Threshold.criticalKappa+1≠0 := by positivity
  have hq : AnalyticAt ℝ Dynamics.conditionQ Threshold.criticalKappa :=
    (hs.sub analyticAt_const).div (hs.add analyticAt_const) hden
  exact analyticAt_log (Threshold.conditionQ_mem Threshold.one_lt_criticalKappa).1
    |>.comp hq

/-- Article: the printed coefficient d(log q)/dκ=1/(4κc). -/
theorem log_conditionQ_hasDerivAt_critical :
    HasDerivAt (fun κ => Real.log (Dynamics.conditionQ κ))
      (1/(4*Threshold.criticalKappa)) Threshold.criticalKappa := by
  let κ := Threshold.criticalKappa
  have hk : κ≠0 := by dsimp [κ]; linarith [Threshold.one_lt_criticalKappa]
  have hs := Real.hasDerivAt_sqrt hk
  have hden : Real.sqrt κ+1≠0 := by positivity
  have hq := ((hs.sub_const 1).div (hs.add_const 1) hden).log
    (ne_of_gt (Threshold.conditionQ_mem Threshold.one_lt_criticalKappa).1)
  have hsq : (Real.sqrt κ)^2=κ := Real.sq_sqrt (by dsimp [κ]; linarith [Threshold.one_lt_criticalKappa])
  have hsqrt : Real.sqrt κ=2*φ+1 := Threshold.sqrt_criticalKappa
  have hgold := Real.goldenRatio_sq
  have hcoef (r : ℝ) (hr : r≠0) (hm : r-1≠0) (hp : r+1≠0) :
      (((1/(2*r))*(r+1)-(r-1)*(1/(2*r)))/(r+1)^2)/((r-1)/(r+1))=
        1/(r*(r^2-1)) := by
    have hr2 : r^2-1≠0 := by
      rw [show r^2-1=(r-1)*(r+1) by ring]
      exact mul_ne_zero hm hp
    field_simp [hr2]
    ring
  have hκ : κ=(2*φ+1)^2 := Threshold.criticalKappa_sq
  have hκrel : Real.sqrt κ*(κ-1)=4*κ := by
    rw [hsqrt,hκ]
    nlinarith [hgold]
  have he : (((1/(2*Real.sqrt κ))*(Real.sqrt κ+1)-
      (Real.sqrt κ-1)*(1/(2*Real.sqrt κ)))/(Real.sqrt κ+1)^2)/
      ((Real.sqrt κ-1)/(Real.sqrt κ+1))=1/(4*κ) := by
    rw [hcoef _ (ne_of_gt (Real.sqrt_pos.mpr (by dsimp [κ]; linarith [Threshold.one_lt_criticalKappa])))
      (by have := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ)≤1) Threshold.one_lt_criticalKappa
          simpa only [Real.sqrt_one] using ne_of_gt (sub_pos.mpr this)) hden,hsq,hκrel]
  change HasDerivAt (fun κ => Real.log (Dynamics.conditionQ κ)) _ κ at hq
  simp only [Pi.div_apply] at hq
  rw [he] at hq
  exact hq

/-- Article: analyticity of the actual rate at the critical condition number. -/
theorem conditionRate_analyticAt_critical :
    AnalyticAt ℝ conditionRate Threshold.criticalKappa := by
  have hqcrit : Dynamics.conditionQ Threshold.criticalKappa=Threshold.criticalQ :=
    (Threshold.conditionQ_eq_critical_iff Threshold.one_lt_criticalKappa).mpr rfl
  have hcomp := logarithmicExponent_analyticAt_critical.comp_of_eq
    log_conditionQ_analyticAt_critical (by rw [hqcrit])
  have hexp := (Real.contDiff_exp.contDiffAt.comp Threshold.criticalKappa hcomp.contDiffAt).analyticAt
  have heq : (fun κ => Real.exp (logarithmicExponent (Real.log (Dynamics.conditionQ κ))))
      =ᶠ[𝓝 Threshold.criticalKappa] conditionRate := by
    have hp : ∀ᶠ κ in 𝓝 Threshold.criticalKappa, 0<Dynamics.conditionQ κ :=
      (eventually_gt_nhds Threshold.one_lt_criticalKappa).mono
        (fun κ hκ => (Threshold.conditionQ_mem hκ).1)
    filter_upwards [hp] with κ hκ
    simp only [logarithmicExponent,Real.exp_log hκ,conditionRate]
  exact hexp.congr heq

/-- Article: the actual original rate has the exact critical slope 1/(4κc). -/
theorem conditionRate_hasDerivAt_critical :
    HasDerivAt conditionRate (1/(4*Threshold.criticalKappa)) Threshold.criticalKappa := by
  have hqcrit : Dynamics.conditionQ Threshold.criticalKappa=Threshold.criticalQ :=
    (Threshold.conditionQ_eq_critical_iff Threshold.one_lt_criticalKappa).mpr rfl
  have hg := HasDerivAt.comp_of_eq Threshold.criticalKappa logarithmicExponent_hasDerivAt_critical
    log_conditionQ_hasDerivAt_critical (by rw [hqcrit])
  have hh := hg.exp
  have heq : (fun κ => Real.exp (logarithmicExponent (Real.log (Dynamics.conditionQ κ))))
      =ᶠ[𝓝 Threshold.criticalKappa] conditionRate := by
    filter_upwards [eventually_gt_nhds Threshold.one_lt_criticalKappa] with κ hκ
    simp only [logarithmicExponent,Real.exp_log (Threshold.conditionQ_mem hκ).1,conditionRate]
  have hval : logarithmicExponent (Real.log (Dynamics.conditionQ Threshold.criticalKappa))=0 := by
    rw [hqcrit,logarithmicExponent_critical]
  simpa only [Function.comp_def,hval,Real.exp_zero,one_mul] using hh.congr_of_eventuallyEq heq.symm

end
end polyak.Regularity

import polyak.Boundary.P5.LocalDual
import polyak.Boundary.P5.LocalFeasible
import polyak.Threshold.Results
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
Article: Theorem p5local, genuine primal–dual optimality and analyticity at the threshold.
Use: the actual two-atom spectrum and exact dual polynomial identify V near zero,
including both signs of the exponent and the critical endpoint itself.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology goldenRatio

/-- Article: every nearby positive h is the true spectral optimum for either sign of the exponent. -/
theorem eventually_localBranch_optimal :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ t : ℝ, Real.cosh t=1+h →
      V t=Real.arsinh (branchU h (localBranch h)) := by
  filter_upwards [eventually_tailBounds localBranch_analyticAt.continuousAt localBranch_zero,
    eventually_branch_primal_prefix,
    eventually_branch_dual_parameters.filter_mono nhdsWithin_le_nhds,
    localBranch_dual_nonneg.filter_mono nhdsWithin_le_nhds] with h hb hprefix hw hQ t ht
  obtain ⟨hx,hy,hb⟩ := hb
  have ht0 : t≠0 := by
    rintro rfl
    norm_num only [Real.cosh_zero] at ht
    linarith [hb.h_pos]
  let W := weights235 (localBranch h 5) (localBranch h 6) hw.1.le hw.2.1.le hw.2.2.1.le
  apply primal_dual_optimal W hb.u_nonneg
    (feasibleU_of_tail_prefix (localBranch h) hx hy hb ht0 ht hprefix)
  intro c
  rw [ht]
  change 0≤(dualPolynomial (weights235 _ _ _ _ _) _ _).eval (c : ℝ)
  rw [dualPolynomial_eq_source (by linarith [hb.h_pos] : (1 : ℝ)<1+h)]
  unfold branchU
  rw [← dualReal_closed]
  exact div_nonneg (hQ hb.h_pos.le c) (commonDenominator_pos (by linarith [hb.h_pos])).le

/-- Article: arsinh(1/2)=log φ, expressed through the independently proved threshold value. -/
theorem critical_boundary_value : V 0=Real.arsinh (1/2) := by
  have h := Threshold.sinh_add_log_golden 0
  norm_num only [zero_add,Real.exp_zero,Real.sinh_zero,zero_div,add_zero] at h
  calc
    V 0=Real.log φ := Threshold.V_zero
    _=Real.arsinh (Real.sinh (Real.log φ)) := (Real.arsinh_sinh _).symm
    _=Real.arsinh (1/2) := congrArg Real.arsinh h

/-- Article: one closed central interval gives the exact boundary, including h=0. -/
theorem exists_local_optimal_interval : ∃ hstar : ℝ, 0<hstar ∧
    ∀ h : ℝ, 0≤h → h≤hstar → ∀ t : ℝ, Real.cosh t=1+h →
      V t=Real.arsinh (branchU h (localBranch h)) := by
  obtain ⟨hstar,hpos,hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp eventually_localBranch_optimal
  refine ⟨hstar,hpos,?_⟩
  intro h hh hmax t ht
  by_cases hz : h=0
  · subst h
    have ht0 : t=0 := by
      by_contra hn
      have hc := Real.one_lt_cosh.mpr hn
      linarith
    subst t
    simpa [branchU] using critical_boundary_value
  · exact hsub ⟨lt_of_le_of_ne hh (Ne.symm hz),hmax⟩ t ht

/-- Article: the actual analytic formula in the exponent variable. -/
def localValue (t : ℝ) : ℝ :=
  Real.arsinh (branchU (Real.cosh t-1) (localBranch (Real.cosh t-1)))

/-- Article: Theorem p5local, one analytic source branch describes the actual boundary near zero. -/
theorem central_family_local : ∃ hstar : ℝ, 0<hstar ∧
    AnalyticOnNhd ℝ localBranch (Set.Ioo (-hstar) hstar) ∧
    (∀ h : ℝ, |h|≤hstar → regularSystem (h,localBranch h)=0) ∧
    (∀ t : ℝ, Real.cosh t≤1+hstar → V t=localValue t) := by
  obtain ⟨δ,hδ,hopt⟩ := exists_local_optimal_interval
  have hg := localBranch_analyticAt.eventually_analyticAt.and localBranch_equations
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hg
  let hstar := min δ (ε/2)
  have hpos : 0<hstar := lt_min hδ (by linarith)
  have hδ' : hstar≤δ := min_le_left _ _
  have hε' : hstar<ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hgood (h : ℝ) (hh : |h|≤hstar) :
      AnalyticAt ℝ localBranch h ∧ regularSystem (h,localBranch h)=0 := by
    apply hball
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hh.trans_lt hε'
  refine ⟨hstar,hpos,?_,?_,?_⟩
  · intro h hh
    exact (hgood h (abs_le.mpr ⟨hh.1.le,hh.2.le⟩)).1
  · intro h hh
    exact (hgood h hh).2
  · intro t ht
    have hh : 0≤Real.cosh t-1 := by linarith [Real.one_le_cosh t]
    exact hopt (Real.cosh t-1) hh (by linarith) t (by ring)

/-- Article: the explicit local boundary formula is real analytic at zero. -/
theorem localValue_analyticAt : AnalyticAt ℝ localValue 0 := by
  have hh : AnalyticAt ℝ (fun t : ℝ => Real.cosh t-1) 0 := by fun_prop
  have hZ : AnalyticAt ℝ (fun t : ℝ => localBranch (Real.cosh t-1)) 0 :=
    localBranch_analyticAt.comp_of_eq hh (by simp)
  have hz : AnalyticAt ℝ (fun t : ℝ => localBranch (Real.cosh t-1) 0) 0 :=
    AnalyticAt.comp (f := fun t : ℝ => localBranch (Real.cosh t-1))
      ((ContinuousLinearMap.proj (0 : Fin 7) : Coordinates →L[ℝ] ℝ).analyticAt
        (localBranch (Real.cosh 0-1))) hZ
  have hu : AnalyticAt ℝ (fun t : ℝ =>
      branchU (Real.cosh t-1) (localBranch (Real.cosh t-1))) 0 := by
    unfold branchU
    exact analyticAt_const.add (hh.mul hz)
  exact Real.analyticAt_arsinh.comp hu

/-- Article: the formula gives the actual spectral boundary on a neighborhood of zero. -/
theorem V_eventually_eq_localValue : V=ᶠ[𝓝 (0 : ℝ)] localValue := by
  obtain ⟨hstar,hpos,_,_,hformula⟩ := central_family_local
  have hc : ContinuousAt Real.cosh 0 := Real.continuous_cosh.continuousAt
  have he := hc.tendsto.eventually (eventually_lt_nhds
    (show Real.cosh (0 : ℝ)<1+hstar by simpa using hpos))
  exact he.mono fun t ht => hformula t ht.le

/-- Article: Theorem p5local, the true boundary is real analytic at the critical exponent. -/
theorem V_analyticAt_zero : AnalyticAt ℝ V 0 :=
  (analyticAt_congr V_eventually_eq_localValue).mpr localValue_analyticAt

/-- Article: the true critical boundary is even and analytic, with its exact threshold value. -/
theorem critical_boundary_even_analytic :
    (∀ t : ℝ, V (-t)=V t) ∧ AnalyticAt ℝ V 0 ∧ V 0=Real.log φ :=
  ⟨V_even,V_analyticAt_zero,Threshold.V_zero⟩

end polyak.Boundary.P5

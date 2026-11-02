import jacobi.Reference.LaplaceEndpoint

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Watson's leading endpoint limit is proved for the original finite-interval
integral with a coefficient only bounded on that interval. A measurable
extension by zero makes no regularity assumption at the far endpoint.
Source: the leading endpoint term of Watson's lemma.
Use: applies directly to the regular coefficient of the actual sine beta density near its selected endpoint in NegativeNormalization.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original finite-interval Laplace integral has its exact leading endpoint coefficient even if the coefficient is bounded only on that interval.
Use: applies directly to the regular coefficient of the actual sine beta density near its selected endpoint in NegativeNormalization.
Article: jacobi, Appendix C.2 (norming ratios).
Source: Watson's leading endpoint lemma, proved from the original Lebesgue integral in LaplaceEndpoint.
Proof: clamp the negative half-line to zero and extend the coefficient
by zero beyond A. This measurable bounded extension is continuous at
zero and agrees with the original coefficient throughout (0,A).
Its original half-line integral is exactly the original interval integral. -/
theorem truncated_laplace_limit {g A : ℝ} (hg : 0<g) (hA : 0<A) {h : ℝ → ℝ}
    (hm : Measurable h) (hc : ContinuousAt h 0)
    (hb : ∃ M : ℝ,0≤M ∧ ∀ s∈Icc (0:ℝ) A,|h s|≤M) :
    Tendsto (fun y : ℝ => y^g*(∫ s in (0:ℝ)..A,Real.exp (-(y*s))*s^(g-1)*h s))
      atTop (𝓝 (Real.Gamma g*h 0)) := by
  classical
  -- The extension controls every real argument while preserving the genuine endpoint value and the original physical interval.
  let H : ℝ → ℝ := (Iic A).indicator (fun s => h (max 0 s))
  have hHm : Measurable H := (hm.comp (measurable_const.max measurable_id)).indicator measurableSet_Iic
  have hHc : ContinuousAt H 0 := by
    have hnear : H=ᶠ[𝓝 (0:ℝ)] (fun s => h (max 0 s)) := by
      filter_upwards [eventually_lt_nhds hA] with s hs
      change (Iic A).indicator (fun s => h (max 0 s)) s=h (max 0 s)
      rw [Set.indicator_of_mem (show s∈Iic A from hs.le)]
    have hh : ContinuousAt (fun s : ℝ => h (max 0 s)) 0 :=
      hc.comp_of_eq (by fun_prop : ContinuousAt (fun s : ℝ => max 0 s) 0) (by simp)
    exact hh.congr_of_eventuallyEq hnear
  obtain ⟨M,hM,hb⟩ := hb
  have hHb : ∃ M : ℝ,0≤M ∧ ∀ s,|H s|≤M := by
    refine ⟨M,hM,fun s => ?_⟩
    by_cases hs : s≤A
    · change |(Iic A).indicator (fun s => h (max 0 s)) s|≤M
      rw [Set.indicator_of_mem (show s∈Iic A from hs)]
      exact hb _ ⟨le_max_left _ _,max_le hA.le hs⟩
    · simpa only [H,Set.indicator_of_notMem (show s∉Iic A from hs),abs_zero] using hM
  have hi (y : ℝ) : (∫ s : ℝ in Ioi 0,Real.exp (-(y*s))*s^(g-1)*H s)=
      ∫ s in (0:ℝ)..A,Real.exp (-(y*s))*s^(g-1)*h s := by
    -- Restricting the original half-line measure gives precisely (0,A], with no contribution from either endpoint.
    have he : (fun s : ℝ => Real.exp (-(y*s))*s^(g-1)*H s)=
        (Iic A).indicator (fun s => Real.exp (-(y*s))*s^(g-1)*h (max 0 s)) := by
      funext s
      by_cases hs : s≤A <;> simp [H,hs]
    rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,
      show Iic A∩Ioi (0:ℝ)=Ioc 0 A by ext s; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc]; tauto,
      intervalIntegral.integral_of_le hA.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [max_eq_right hs.1.le]
  have hl := laplace_endpoint_limit hg hHm hHc hHb
  have hH0 : H 0=h 0 := by simp [H,hA.le]
  simpa only [hi,hH0] using hl

end
end jacobi.Reference

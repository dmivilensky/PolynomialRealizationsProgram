import krylov.AnalyticTools.PicardImplicit
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Article: main_krylov, apC:prop:LV, analytic ODE background.
Use: identify the analytic Picard family with a genuine integral curve through
the locally unique implicit equation. Analyticity of a concrete lifted field
can therefore be used without an additional analytic-flow axiom.
Source: the compact-open topology, analytic implicit uniqueness, and the FTC.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An actual continuous curve, viewed on a rescaled unit time window. -/
def rescaledPath {α : ℝ → E} (hc : Continuous α) (t₀ t : ℝ) : C(PathDomain, E) where
  toFun u := α (t₀ + t * (u : ℝ))
  continuous_toFun := hc.comp (by fun_prop)

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem continuous_rescaledPath {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ) :
    Continuous (rescaledPath hc t₀) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hc.comp (by fun_prop)

/-- A locally satisfied Picard equation for a real curve transfers analytic
regularity from the Banach-space implicit construction to that actual curve. -/
theorem analyticAt_of_rescaled_picard
    {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ)
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : AnalyticAt ℝ P (ContinuousMap.const PathDomain (α t₀)))
    (hfix : ∀ᶠ t in 𝓝 (0 : ℝ), rescaledPath hc t₀ t =
      ContinuousMap.const PathDomain (α t₀) +
        t • pathIntegralCLM (P (rescaledPath hc t₀ t))) :
    AnalyticAt ℝ (fun t ↦ α (t₀ + t)) 0 := by
  obtain ⟨w, hw, _, _, huniq⟩ := exists_analytic_picard_family P (α t₀) hP
  have hzero : rescaledPath hc t₀ 0 = ContinuousMap.const PathDomain (α t₀) := by
    ext u
    simp [rescaledPath]
  have ht : Tendsto (fun t : ℝ ↦ (t, rescaledPath hc t₀ t)) (𝓝 0)
      (𝓝 ((0 : ℝ), ContinuousMap.const PathDomain (α t₀))) := by
    have ht₀ := (continuous_id.prodMk (continuous_rescaledPath hc t₀)).continuousAt
      (x := (0 : ℝ))
    change Tendsto (fun t : ℝ ↦ (t, rescaledPath hc t₀ t)) (𝓝 0)
      (𝓝 ((0 : ℝ), rescaledPath hc t₀ 0)) at ht₀
    rwa [hzero] at ht₀
  have heq : (fun t ↦ (w t) (⟨1, by norm_num⟩ : PathDomain)) =ᶠ[𝓝 0]
      (fun t ↦ α (t₀ + t)) := by
    filter_upwards [ht.eventually huniq, hfix] with t hu hf
    have h := congrArg (fun f : C(PathDomain, E) ↦ f (⟨1, by norm_num⟩ : PathDomain))
      (hu hf)
    simpa only [rescaledPath, ContinuousMap.coe_mk, mul_one] using h.symm
  let e : C(PathDomain, E) →L[ℝ] E :=
    ContinuousMap.evalCLM (R := ℝ) (⟨1, by norm_num⟩ : PathDomain)
  exact ((e.analyticAt _).comp hw).congr heq

/-- A genuine local differential equation supplies the rescaled integral
equation. The path field must agree pointwise with the displayed vector field. -/
theorem rescaled_picard_of_eventually_lift
    {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ) {F : E → E}
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain (α t₀)), ∀ u, P f u = F (f u))
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (F (α t)) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ), rescaledPath hc t₀ t =
      ContinuousMap.const PathDomain (α t₀) +
        t • pathIntegralCLM (P (rescaledPath hc t₀ t)) := by
  obtain ⟨δ, hδ, hδd⟩ := Metric.eventually_nhds_iff.mp hd
  have hpath : Tendsto (rescaledPath hc t₀) (𝓝 0)
      (𝓝 (ContinuousMap.const PathDomain (α t₀))) := by
    have hh := (continuous_rescaledPath hc t₀).continuousAt (x := (0 : ℝ))
    change Tendsto (rescaledPath hc t₀) (𝓝 0) (𝓝 (rescaledPath hc t₀ 0)) at hh
    have hzero : rescaledPath hc t₀ 0 = ContinuousMap.const PathDomain (α t₀) := by
      ext u
      simp [rescaledPath]
    rwa [hzero] at hh
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ, hpath.eventually hP] with t ht hmatch
  have htδ : |t| < δ := by simpa [Real.dist_eq] using ht
  have hdv (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun v ↦ α (t₀ + t * v)) (t • F (α (t₀ + t * v))) v := by
    have hnear : dist (t₀ + t * v) t₀ < δ := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_nonneg hv.1]
      exact (mul_le_of_le_one_right (abs_nonneg _) hv.2).trans_lt htδ
    have htder : HasDerivAt (fun v : ℝ ↦ t₀ + t * v) t v := by
      convert (hasDerivAt_const v t₀).add
        ((hasDerivAt_const v t).mul (hasDerivAt_id v)) using 1 <;>
        first | rfl | simp only [zero_mul, zero_add, mul_one]
    exact (hδd hnear).scomp v htder
  ext u
  have hprimitive : pathIntegralCLM (P (rescaledPath hc t₀ t)) u =
      ∫ v in 0..(u : ℝ), F (α (t₀ + t * v)) := by
    rw [pathIntegralCLM_apply]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le u.2.1] at hv
    have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨hv.1, hv.2.trans u.2.2⟩
    simp only [extendPath, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hv']
    rw [hmatch]
    rfl
  have hint : IntervalIntegrable
      (fun v ↦ t • F (α (t₀ + t * v))) volume 0 (u : ℝ) := by
    apply ((continuous_extendPath (P (rescaledPath hc t₀ t))).const_smul t).intervalIntegrable
      (0 : ℝ) (u : ℝ) |>.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
    have hv' : v ∈ Icc (0 : ℝ) 1 := by
      have hv₀ := uIoc_subset_uIcc hv
      rw [uIcc_of_le u.2.1] at hv₀
      exact ⟨hv₀.1, hv₀.2.trans u.2.2⟩
    change t • extendPath (P (rescaledPath hc t₀ t)) v = t • F (α (t₀ + t * v))
    simp only [extendPath, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hv']
    rw [hmatch]
    rfl
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv ↦ hdv v (by
      rw [uIcc_of_le u.2.1] at hv
      exact ⟨hv.1, hv.2.trans u.2.2⟩)) hint
  rw [intervalIntegral.integral_smul] at hi
  change α (t₀ + t * (u : ℝ)) = α t₀ + t • _
  rw [hprimitive]
  have hi' : t • (∫ v in 0..(u : ℝ), F (α (t₀ + t * v))) =
      α (t₀ + t * (u : ℝ)) - α t₀ := by simpa using hi
  exact (sub_eq_iff_eq_add.mp hi'.symm).trans (add_comm _ _)

/-- Globally defined pointwise lifts are a special case of the local theorem. -/
theorem rescaled_picard_of_hasDerivAt
    {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ) {F : E → E}
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ f u, P f u = F (f u))
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (F (α t)) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ), rescaledPath hc t₀ t =
      ContinuousMap.const PathDomain (α t₀) +
        t • pathIntegralCLM (P (rescaledPath hc t₀ t)) :=
  rescaled_picard_of_eventually_lift hc t₀ P (Eventually.of_forall hP) hd

/-- Local agreement of an analytic path lift is sufficient for actual ODE
analyticity. Rational fields need only be invertible near the initial path. -/
theorem analyticAt_of_eventually_lifted_field
    {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ) {F : E → E}
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain (α t₀)), ∀ u, P f u = F (f u))
    (ha : AnalyticAt ℝ P (ContinuousMap.const PathDomain (α t₀)))
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (F (α t)) t) :
    AnalyticAt ℝ (fun t ↦ α (t₀ + t)) 0 :=
  analyticAt_of_rescaled_picard hc t₀ P ha
    (rescaled_picard_of_eventually_lift hc t₀ P hP hd)

/-- Real analyticity of an actual ODE solution follows from analyticity of
the pointwise lifted field on continuous paths. -/
theorem analyticAt_of_lifted_field
    {α : ℝ → E} (hc : Continuous α) (t₀ : ℝ) {F : E → E}
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ f u, P f u = F (f u))
    (ha : AnalyticAt ℝ P (ContinuousMap.const PathDomain (α t₀)))
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (F (α t)) t) :
    AnalyticAt ℝ (fun t ↦ α (t₀ + t)) 0 :=
  analyticAt_of_rescaled_picard hc t₀ P ha
    (rescaled_picard_of_hasDerivAt hc t₀ P hP hd)

/-- Local analytic ODE regularity with a locally agreeing path lift. Values
of the actual curve and of the rational field away from the initial point
need no extension hypotheses. -/
theorem analyticAt_of_local_lifted_field {α : ℝ → E} {t₀ : ℝ} {F : E → E}
    (P : C(PathDomain, E) → C(PathDomain, E))
    (hP : ∀ᶠ f in 𝓝 (ContinuousMap.const PathDomain (α t₀)), ∀ u, P f u = F (f u))
    (ha : AnalyticAt ℝ P (ContinuousMap.const PathDomain (α t₀)))
    (hd : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (F (α t)) t) : AnalyticAt ℝ α t₀ := by
  obtain ⟨δ, hδ, hδd⟩ := Metric.eventually_nhds_iff.mp hd
  let a := t₀ - δ / 2
  let b := t₀ + δ / 2
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hα : ContinuousOn α (Icc a b) := by
    intro t ht
    have hnear : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      dsimp [a, b] at ht
      constructor <;> linarith [ht.1, ht.2]
    exact (hδd hnear).continuousAt.continuousWithinAt
  let β : ℝ → E := fun t ↦ α (projIcc a b hab t)
  have hβ : Continuous β := hα.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t ↦ (projIcc a b hab t).2)
  have heq : β =ᶠ[𝓝 t₀] α := by
    have hI : Ioo a b ∈ 𝓝 t₀ := Ioo_mem_nhds
      (by dsimp [a]; linarith) (by dsimp [b]; linarith)
    filter_upwards [hI] with t ht
    change α (projIcc a b hab t) = α t
    rw [projIcc_of_mem hab ⟨ht.1.le, ht.2.le⟩]
  have hdβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (F (β t)) t := by
    filter_upwards [hd, heq.eventuallyEq_nhds, heq] with t ht he htEq
    rw [htEq]
    exact ht.congr_of_eventuallyEq he
  have haβ : AnalyticAt ℝ (fun t ↦ β (t₀ + t)) 0 :=
    analyticAt_of_eventually_lifted_field hβ t₀ P
      (by simpa only [heq.self_of_nhds] using hP)
      (by simpa only [heq.self_of_nhds] using ha) hdβ
  have hsub : AnalyticAt ℝ (fun t : ℝ ↦ t - t₀) t₀ :=
    analyticAt_id.sub analyticAt_const
  have hcomp := haβ.comp_of_eq hsub (by simp)
  have haβ' : AnalyticAt ℝ β t₀ := by
    simpa only [Function.comp_def, add_sub_cancel] using hcomp
  exact haβ'.congr heq

end
end krylov.AnalyticTools

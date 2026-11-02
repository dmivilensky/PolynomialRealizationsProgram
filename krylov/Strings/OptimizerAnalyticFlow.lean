import krylov.LotkaVolterra.AnalyticFlow
import krylov.Strings.OptimizerPhysicalExtension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import krylov.AnalyticTools.RightFlow
import krylov.AnalyticTools.RightChange
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
Article: main_krylov, thm:value, analyticity of the optimizing density.
Use: augment the actual LV curve by its physical quadratures. Introducing
w=exp(-τ) makes the entire augmented field polynomial, so the existing
analytic Picard theorem applies without an analytic substitution theorem
on spaces of functions. The inverse physical clock then preserves analyticity.
Source: analytic ODE regularity, FTC and mathlib's analytic inverse theorem.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter
open krylov.AnalyticTools
open scoped Topology

private abbrev AugmentedState := Fin 5 → ℝ

private def coord (i : Fin 5) : C(PathDomain, AugmentedState) →L[ℝ] C(PathDomain, ℝ) :=
  (ContinuousLinearMap.proj i).compLeftContinuous ℝ PathDomain

private def insert (i : Fin 5) : C(PathDomain, ℝ) →L[ℝ] C(PathDomain, AugmentedState) :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin 5 ↦ ℝ) i).compLeftContinuous ℝ PathDomain

private theorem coord_apply (i : Fin 5) (f : C(PathDomain, AugmentedState)) (u : PathDomain) :
    coord i f u = f u i := rfl

private theorem insert_apply (i : Fin 5) (f : C(PathDomain, ℝ)) (u : PathDomain) :
    insert i f u = Pi.single i (f u) := rfl

private def augmentedField (γ : ℝ) (z : AugmentedState) : AugmentedState :=
  ![2 * z 0 * (z 0 - 1 - γ * z 1), z 1 * (z 0 + 1 - z 1), z 0 * z 2,
    -z 3, z 2 * z 0 * z 3]

private def augmentedLift (γ : ℝ) (f : C(PathDomain, AugmentedState)) :
    C(PathDomain, AugmentedState) :=
  insert 0 (ContinuousMap.const PathDomain 2 * coord 0 f *
    (coord 0 f - 1 - ContinuousMap.const PathDomain γ * coord 1 f)) +
  insert 1 (coord 1 f * (coord 0 f + 1 - coord 1 f)) +
  insert 2 (coord 0 f * coord 2 f) + insert 3 (-coord 3 f) +
  insert 4 (coord 2 f * coord 0 f * coord 3 f)

private theorem augmentedLift_apply (γ : ℝ) (f : C(PathDomain, AugmentedState))
    (u : PathDomain) : augmentedLift γ f u = augmentedField γ (f u) := by
  ext i
  fin_cases i <;> simp [augmentedLift, augmentedField, insert_apply, coord_apply]

private theorem augmentedLift_analytic (γ : ℝ) (f : C(PathDomain, AugmentedState)) :
    AnalyticAt ℝ (augmentedLift γ) f := by
  have h (i : Fin 5) := (coord i).analyticAt f
  have h₀ : AnalyticAt ℝ (fun f ↦ ContinuousMap.const PathDomain 2 * coord 0 f *
      (coord 0 f - 1 - ContinuousMap.const PathDomain γ * coord 1 f)) f :=
    (analyticAt_const.mul (h 0)).mul
      (((h 0).sub analyticAt_const).sub (analyticAt_const.mul (h 1)))
  have h₁ : AnalyticAt ℝ (fun f ↦ coord 1 f * (coord 0 f + 1 - coord 1 f)) f :=
    (h 1).mul (((h 0).add analyticAt_const).sub (h 1))
  have h₂ := (h 0).mul (h 2)
  have h₃ := (h 3).neg
  have h₄ := ((h 2).mul (h 0)).mul (h 3)
  exact (((((insert 0).analyticAt _).comp h₀).add (((insert 1).analyticAt _).comp h₁)).add
    (((insert 2).analyticAt _).comp h₂)).add (((insert 3).analyticAt _).comp h₃) |>.add
      (((insert 4).analyticAt _).comp h₄)

private def augmentedCurve (s U : ℝ → ℝ) (t : ℝ) : AugmentedState :=
  ![s t, U t, expPrimitive s t, Real.exp (-t), physicalClock s t]

private theorem augmentedCurve_hasDerivAt {γ t : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s)
    (hd : HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    HasDerivAt (augmentedCurve s U) (augmentedField γ (augmentedCurve s U t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [augmentedCurve, augmentedField] using hd.1
  · simpa [augmentedCurve, augmentedField] using hd.2
  · simpa [augmentedCurve, augmentedField] using expPrimitive_derivative hs t
  · convert! ((hasDerivAt_id t).neg).exp using 1
    simp [augmentedCurve, augmentedField]
  · have he : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    simpa [augmentedCurve, augmentedField, physicalSpeed, he, div_eq_mul_inv] using
      physicalClock_derivative hs t

/-- The actual position quadrature and physical clock are analytic wherever
the underlying LV equations hold on a neighborhood. -/
theorem analyticAt_physical_quadratures {γ t : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s)
    (hd : ∀ᶠ u in 𝓝 t, HasDerivAt s (2 * s u * (s u - 1 - γ * U u)) u ∧
      HasDerivAt U (U u * (s u + 1 - U u)) u) :
    AnalyticAt ℝ s t ∧ AnalyticAt ℝ (expPrimitive s) t ∧ AnalyticAt ℝ (physicalClock s) t := by
  have hα : ∀ᶠ u in 𝓝 t, HasDerivAt (augmentedCurve s U)
      (augmentedField γ (augmentedCurve s U u)) u :=
    hd.mono (fun _ hu ↦ augmentedCurve_hasDerivAt hs hu)
  have ha := analyticAt_of_local_lifted_field (augmentedLift γ)
    (Eventually.of_forall (augmentedLift_apply γ)) (augmentedLift_analytic γ _) hα
  have h (i : Fin 5) := ((ContinuousLinearMap.proj i : AugmentedState →L[ℝ] ℝ).analyticAt _).comp ha
  exact ⟨by simpa [augmentedCurve, Function.comp_def] using h 0,
    by simpa [augmentedCurve, Function.comp_def] using h 2, by simpa [augmentedCurve, Function.comp_def] using h 4⟩

/-- The positive density of the constructed genuine mass is real analytic
at every positive physical position. -/
theorem analyticAt_extendedDensity {γ x : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) (hx : 0 < x) :
    AnalyticAt ℝ (extendedDensity s) x := by
  let t := inverseClock s x
  have ht : 0 < t := by
    apply (physicalClock_strictMono hs hp).lt_iff_lt.mp
    change physicalClock s 0 < physicalClock s (Function.invFun (physicalClock s) x)
    rw [inverseClock_right_inverse hs hp h₁ hx.le, physicalClock_zero]
    exact hx
  have hd : ∀ᶠ u in 𝓝 t, HasDerivAt s (2 * s u * (s u - 1 - γ * U u)) u ∧
      HasDerivAt U (U u * (s u + 1 - U u)) u :=
    Filter.Eventually.mono (show ∀ᶠ u in 𝓝 t, 0 < u from Ioi_mem_nhds ht)
      (fun u hu ↦ hode u hu)
  obtain ⟨hsa, hφa, hxa⟩ := analyticAt_physical_quadratures hs hd
  have hsqrt := analyticAt_sqrt_comp hsa (hp t)
  have hρ : AnalyticAt ℝ (densityInOrbitTime s) t := by
    exact analyticAt_id.rexp'.div (hφa.mul hsqrt)
      (mul_ne_zero (expPrimitive_pos s t).ne' (Real.sqrt_pos.mpr (hp t)).ne')
  have hder : deriv (physicalClock s) t ≠ 0 := by
    rw [(physicalClock_derivative hs t).deriv]
    exact (physicalSpeed_pos hp t).ne'
  have hcomp : AnalyticAt ℝ (extendedDensity s ∘ physicalClock s) t := by
    apply hρ.congr
    have hcx := (physicalClock_derivative hs t).continuousAt
    have hix : physicalClock s t = x := inverseClock_right_inverse hs hp h₁ hx.le
    have hev : ∀ᶠ y in 𝓝 (physicalClock s t), extendedPullback s (densityInOrbitTime s) y =
        densityInOrbitTime s (inverseClock s y) := by
      rw [hix]
      exact extendedPullback_eventually hs hp (densityInOrbitTime s) hx.le
    have heq := hcx.tendsto.eventually hev
    filter_upwards [heq] with u hu
    rw [Function.comp_apply, extendedDensity, hu]
    rw [inverseClock, Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective]
  have ha := (analyticAt_comp_iff_of_deriv_ne_zero hxa hder).mp hcomp
  have hix : physicalClock s t = x := inverseClock_right_inverse hs hp h₁ hx.le
  rwa [hix] at ha

private theorem augmentedField_contDiff (γ : ℝ) : ContDiff ℝ 1 (augmentedField γ) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [augmentedField] <;> fun_prop

private theorem augmentedCurve_continuous {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) : Continuous (augmentedCurve s U) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact hs
  · exact hU
  · exact expPrimitive_continuous hs
  · exact Real.continuous_exp.comp continuous_neg
  · exact continuous_iff_continuousAt.mpr (fun t ↦ (physicalClock_derivative hs t).continuousAt)

/-- The actual constructed density has an analytic right germ at its initial
point. Its arbitrary negative-time extension need not be analytic there. -/
theorem analyticWithinAt_extendedDensity_zero {γ : ℝ} {s U : ℝ → ℝ}
    (hs : Continuous s) (hU : Continuous U) (hp : ∀ t, 0 < s t)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t)
    (hode : ∀ t > 0, HasDerivAt s (2 * s t * (s t - 1 - γ * U t)) t ∧
      HasDerivAt U (U t * (s t + 1 - U t)) t) :
    AnalyticWithinAt ℝ (extendedDensity s) (Ici 0) 0 := by
  let α := augmentedCurve s U
  have hcα : Continuous α := augmentedCurve_continuous hs hU
  have hdpos (t : ℝ) (ht : 0 < t) : HasDerivAt α (augmentedField γ (α t)) t :=
    augmentedCurve_hasDerivAt hs (hode t ht)
  have hdz : HasDerivWithinAt α (augmentedField γ (α 0)) (Ici 0) 0 := by
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (s := Ioi 0) (fun t ht ↦ (hdpos t ht).differentiableAt.differentiableWithinAt)
      hcα.continuousAt.continuousWithinAt self_mem_nhdsWithin
    have hlim : Tendsto (fun t ↦ augmentedField γ (α t)) (𝓝[>] 0)
        (𝓝 (augmentedField γ (α 0))) :=
      ((augmentedField_contDiff γ).continuous.comp hcα).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hdpos t ht).deriv.symm
  have hdα (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt α (augmentedField γ (α t)) (Ici 0) t := by
    rcases eq_or_lt_of_le ht with rfl | ht
    · exact hdz
    · exact (hdpos t ht).hasDerivWithinAt
  obtain ⟨β, hβ, hβ₀, heq, hdβ⟩ := exists_analytic_right_extension
    (fun z ↦ (augmentedField_contDiff γ).contDiffAt (x := z)) (augmentedLift γ)
    (augmentedLift_apply γ) (fun z ↦ augmentedLift_analytic γ _)
    hcα.continuousOn hdα
  have h (i : Fin 5) : AnalyticAt ℝ (fun t ↦ β t i) 0 := by
    convert! ((ContinuousLinearMap.proj i : AugmentedState →L[ℝ] ℝ).analyticAt _).comp hβ using 1
  let q : ℝ → ℝ := fun t ↦ β t 4
  let ρ : ℝ → ℝ := fun t ↦ 1 / (β t 2 * Real.sqrt (β t 0) * β t 3)
  have hβs : 0 < β 0 0 := by simpa [hβ₀, α, augmentedCurve] using hp 0
  have hβφ : β 0 2 = 1 := by simp [hβ₀, α, augmentedCurve]
  have hβw : β 0 3 = 1 := by simp [hβ₀, α, augmentedCurve]
  have hq : AnalyticAt ℝ q 0 := h 4
  have hρ : AnalyticAt ℝ ρ 0 :=
    analyticAt_const.div (((h 2).mul (analyticAt_sqrt_comp (h 0) hβs)).mul (h 3))
      (by rw [hβφ, hβw]; simpa using (Real.sqrt_pos.mpr hβs).ne')
  have hq₀ : q 0 = 0 := by simp [q, hβ₀, α, augmentedCurve]
  have hqd : HasDerivAt q (s 0) 0 := by
    have hh := (ContinuousLinearMap.proj (4 : Fin 5) : AugmentedState →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0
      hdβ.self_of_nhds
    convert! hh using 1
    simp [augmentedField, hβ₀, α, augmentedCurve]
  have hQ : physicalClock s =ᶠ[𝓝[Ici 0] 0] q := by
    filter_upwards [heq] with t ht
    exact congrFun ht (4 : Fin 5)
  have hR : densityInOrbitTime s =ᶠ[𝓝[Ici 0] 0] ρ := by
    filter_upwards [heq] with t ht
    change densityInOrbitTime s t = 1 / (β t 2 * Real.sqrt (β t 0) * β t 3)
    rw [← ht]
    dsimp [α, augmentedCurve, densityInOrbitTime]
    rw [Real.exp_neg]
    field_simp [(Real.exp_ne_zero t), (expPrimitive_pos s t).ne', (Real.sqrt_pos.mpr (hp t)).ne']
  apply analyticWithinAt_right_change hq hρ hq₀
    (by rw [hqd.deriv]; exact (hp 0).ne')
    (inverseClock_derivative_nonneg hs hp h₁ le_rfl).continuousAt
    (inverseClock_zero hs hp) (fun x hx ↦ inverseClock_nonneg hs hp h₁ hx)
    (fun x hx ↦ inverseClock_right_inverse hs hp h₁ hx) hQ hR
  exact (extendedPullback_eventually hs hp (densityInOrbitTime s) le_rfl).filter_mono nhdsWithin_le_nhds

end
end krylov.Strings.OptimizerQuadratures

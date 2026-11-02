import krylov.Design.HyperbolicDual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SumIntegralComparisons

/-!
Article: main_krylov, apC:lem:poisson, exact zero-frequency hyperbolic integrals.
Use: establish the genuine sech integrability and integral pi by a real
primitive, reusing the already proved even-derivative integrability theorem.
Source: the elementary primitive arctan(sinh x); mathlib supplies the improper
fundamental theorem of calculus and arctangent endpoint limits.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology

/-- The actual hyperbolic secant has the elementary primitive arctan(sinh x).
Article: main_krylov, apC:lem:poisson. -/
theorem arctan_sinh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => arctan (sinh y)) (sech x) x := by
  have h := (Real.hasDerivAt_arctan (sinh x)).comp x (Real.hasDerivAt_sinh x)
  convert! h using 1
  rw [sech]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The positive-end limit of the actual secant primitive.
Article: main_krylov, apC:lem:poisson. -/
theorem arctan_sinh_atTop : Tendsto (fun x : ℝ => arctan (sinh x)) atTop (𝓝 (π / 2)) := by
  have hs : Tendsto sinh atTop atTop :=
    tendsto_atTop_mono' atTop ((eventually_ge_atTop (0 : ℝ)).mono
      (fun x hx => Real.self_le_sinh_iff.mpr hx)) tendsto_id
  exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hs

/-- The negative-end limit of the actual secant primitive.
Article: main_krylov, apC:lem:poisson. -/
theorem arctan_sinh_atBot : Tendsto (fun x : ℝ => arctan (sinh x)) atBot (𝓝 (-(π / 2))) := by
  have h := (arctan_sinh_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, Real.sinh_neg, Real.arctan_neg, neg_neg] using h

/-- The actual hyperbolic secant is integrable on the full real line.
Article: main_krylov, apC:lem:poisson.
Proof: reuse the previous package's positive even derivative criterion with the actual arctangent primitive. -/
theorem sech_integrable : Integrable sech := by
  apply integrable_even_derivative (g := fun x : ℝ => arctan (sinh x)) (a := π / 2)
  · exact Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')
  · intro x
    exact (sech_pos x).le
  · exact sech_neg
  · exact arctan_sinh_hasDerivAt
  · exact arctan_sinh_atTop

/-- The exact whole-line zero-frequency secant transform is pi.
Article: main_krylov, apC:lem:poisson. -/
theorem integral_sech : (∫ x : ℝ, sech x) = π := by
  have h := integral_of_hasDerivAt_of_tendsto arctan_sinh_hasDerivAt sech_integrable
    arctan_sinh_atBot arctan_sinh_atTop
  convert! h using 1
  ring

/-- The exact positive-half-line secant integral is pi/2.
Article: main_krylov, apC:lem:poisson. -/
theorem integral_Ioi_sech : (∫ x : ℝ in Set.Ioi 0, sech x) = π / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (arctan_sinh_hasDerivAt 0).continuousAt.continuousWithinAt
    (fun x (_ : x ∈ Set.Ioi 0) => arctan_sinh_hasDerivAt x)
    sech_integrable.integrableOn arctan_sinh_atTop
  simpa using h

end
end krylov.Design

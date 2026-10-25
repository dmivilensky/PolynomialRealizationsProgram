import polyak.Boundary.P1.Source
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Article: Proposition P₁, transfer from the checked source slope to the actual boundary.
Use: z=1/cosh t has squared derivative z²(1−z²), so the source's strict
algebraic slope inequality is exactly |V′(t)|<1 after composition with arsinh.
-/
noncomputable section
namespace polyak.Boundary.P1
open Filter
open scoped Topology

/-- Exact derivative of the physical reciprocal-cosh parameter. -/
theorem reciprocal_cosh_hasDerivAt (t : ℝ) :
    HasDerivAt (fun r : ℝ => (Real.cosh r)⁻¹)
      (-Real.sinh t/(Real.cosh t)^2) t := by
  convert (Real.hasDerivAt_cosh t).inv (Real.cosh_pos t).ne' using 1

/-- The source slope checker uses precisely the square of the physical derivative. -/
theorem reciprocal_cosh_derivative_sq (t : ℝ) :
    (-Real.sinh t/(Real.cosh t)^2)^2=
      (Real.cosh t)⁻¹^2*(1-(Real.cosh t)⁻¹^2) := by
  have hc : Real.cosh t≠0 := (Real.cosh_pos t).ne'
  have hh:=Real.cosh_sq_sub_sinh_sq t
  field_simp [hc]
  nlinarith [hh]

/-- Exact analytic chain rule, retaining the source derivative's value. -/
theorem hasDerivAt_boundary_of_source {u : ℝ → ℝ} {t du : ℝ}
    (hu : HasDerivAt u du (Real.cosh t)⁻¹) :
    HasDerivAt (fun r => Real.arsinh (u (Real.cosh r)⁻¹))
      (du*(-Real.sinh t/(Real.cosh t)^2)/Real.sqrt (1+(u (Real.cosh t)⁻¹)^2)) t := by
  have hd := (hu.comp t (reciprocal_cosh_hasDerivAt t)).arsinh
  convert hd using 1
  · funext r
    rfl
  · simp only [Function.comp_apply,smul_eq_mul]
    ring

/-- Every strict checked scalar source inequality gives the actual strict boundary slope.
The local formula identifies V itself, rather than an unproved proposed branch. -/
theorem abs_deriv_boundary_lt_one {u V : ℝ → ℝ} {t du : ℝ}
    (hu : HasDerivAt u du (Real.cosh t)⁻¹)
    (hformula : V=ᶠ[𝓝 t] (fun r => Real.arsinh (u (Real.cosh r)⁻¹)))
    (hstrict : du^2*((Real.cosh t)⁻¹)^2*(1-((Real.cosh t)⁻¹)^2)<
      1+(u (Real.cosh t)⁻¹)^2) : |deriv V t|<1 := by
  have hs : 0<Real.sqrt (1+(u (Real.cosh t)⁻¹)^2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hsq : (du*(-Real.sinh t/(Real.cosh t)^2))^2<
      (Real.sqrt (1+(u (Real.cosh t)⁻¹)^2))^2 := by
    rw [mul_pow,reciprocal_cosh_derivative_sq,Real.sq_sqrt (by positivity)]
    nlinarith [hstrict]
  have hnum : |du*(-Real.sinh t/(Real.cosh t)^2)|<
      Real.sqrt (1+(u (Real.cosh t)⁻¹)^2) := by
    apply (sq_lt_sq₀ (abs_nonneg _) hs.le).mp
    simpa only [sq_abs] using hsq
  have hd := (hasDerivAt_boundary_of_source hu).congr_of_eventuallyEq hformula
  rw [hd.deriv,abs_div,abs_of_pos hs]
  exact (div_lt_one hs).mpr hnum

end polyak.Boundary.P1

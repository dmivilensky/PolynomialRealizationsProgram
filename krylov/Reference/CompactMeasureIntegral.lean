import krylov.Realization.RawJacobi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Use: derive polynomial integrability, normalization and both localizing square inequalities from the genuine measure support.
Source: mathlib compact integrability and positivity of the Bochner integral.
-/

namespace krylov.Reference
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

/-- Every polynomial is integrable against the original finite compactly supported measure.
Use: Every polynomial is integrable against the original finite compactly supported measure.
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Proof: Use continuous integrability on the compact physical interval and the actual almost everywhere support. -/
theorem polynomial_integrable_compact (sigma : Measure ℝ) [IsFiniteMeasure sigma]
    (I : chebyshev1.SpectralInterval) (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) (p : ℝ[X]) :
    Integrable (fun x => p.eval x) sigma := by
  -- Compact polynomial integrability extends to the whole measure through its actual almost everywhere support.
  have h := p.continuous.continuousOn.integrableOn_compact (μ := sigma) (isCompact_Icc (a := I.mu) (b := I.L))
  have he : Set.Icc I.mu I.L=ᵐ[sigma] (Set.univ : Set ℝ) := by
    filter_upwards [hI] with x hx
    simp only [Set.mem_univ]
    exact propext (iff_true_intro hx)
  rw [integrableOn_congr_set_ae he,integrableOn_univ] at h
  exact h

/-- The genuine polynomial integral of the original compactly supported spectral measure.
Use: The genuine polynomial integral of the original compactly supported spectral measure.
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Proof: Polynomial integrability gives additivity and scalar linearity of the actual integral. -/
def measurePolynomialIntegral (sigma : Measure ℝ) [IsFiniteMeasure sigma]
    (I : chebyshev1.SpectralInterval) (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x,p.eval x ∂sigma
  map_add' p q := by
    simp only [eval_add]
    exact integral_add (polynomial_integrable_compact sigma I hI p) (polynomial_integrable_compact sigma I hI q)
  map_smul' a p := by
    simp only [eval_smul,smul_eq_mul,RingHom.id_apply]
    exact integral_const_mul _ _

/-- The genuine polynomial functional of the original probability measure is normalized.
Use: The genuine polynomial functional of the original probability measure is normalized.
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Proof: Evaluate the integral of the constant polynomial in the actual probability measure. -/
theorem measurePolynomialIntegral_one (sigma : Measure ℝ) [IsProbabilityMeasure sigma]
    (I : chebyshev1.SpectralInterval) (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) :
    measurePolynomialIntegral sigma I hI 1=1 := by
  simp [measurePolynomialIntegral]

/-- The original lower support endpoint makes every localizing polynomial square integral nonnegative.
Use: The original lower support endpoint makes every localizing polynomial square integral nonnegative.
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Proof: Integrate the actual nonnegative product on the almost everywhere physical support. -/
theorem measurePolynomialIntegral_lower (sigma : Measure ℝ) [IsFiniteMeasure sigma]
    (I : chebyshev1.SpectralInterval) (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) (p : ℝ[X]) :
    0≤measurePolynomialIntegral sigma I hI ((X-C I.mu)*p^2) := by
  apply integral_nonneg_of_ae
  filter_upwards [hI] with x hx
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_pow]
  exact mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _)

/-- The original upper support endpoint makes every localizing polynomial square integral nonnegative.
Use: The original upper support endpoint makes every localizing polynomial square integral nonnegative.
Article: main_krylov, prop:phi(c), the original compactly supported spectral integral.
Proof: Integrate the actual nonnegative product on the almost everywhere physical support. -/
theorem measurePolynomialIntegral_upper (sigma : Measure ℝ) [IsFiniteMeasure sigma]
    (I : chebyshev1.SpectralInterval) (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) (p : ℝ[X]) :
    0≤measurePolynomialIntegral sigma I hI ((C I.L-X)*p^2) := by
  apply integral_nonneg_of_ae
  filter_upwards [hI] with x hx
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_pow]
  exact mul_nonneg (sub_nonneg.mpr hx.2) (sq_nonneg _)
end
end krylov.Reference

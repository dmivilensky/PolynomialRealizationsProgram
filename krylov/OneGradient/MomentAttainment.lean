import krylov.OneGradient.AtomicProbability
import krylov.OneGradient.SupportedMomentCompletion
import krylov.Reference.GradientMeasureInvariance
import krylov.LinearAlgebra.NormOrder
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), genuine probability-measure attainment.
Use: realize every actual physical spectral completion by a true supported
probability measure with exactly the source's fixed and missing moments.
Source: the proved actual weighted Dirac probability construction, original
gradient spectral data and genuine physical eigenvalue interval tests.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix MeasureTheory krylov.Reference krylov.LinearAlgebra
variable {m n : ℕ}

/-- The actual normalized gradient spectral probability measure of the original physical matrix.
Use: actual endpoint attainment belongs to the same all-probability-measure class.
Article: main_krylov, s5:moment(b). -/
def gradientProbabilityMeasure (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (hg : g≠0) : Measure ℝ :=
  discreteAtomicMeasure (gradientSpectralData A hA g hg)

/-- The actual original physical gradient measure is a true probability measure.
Use: physical spectral completions give genuine admissible candidate measures.
Article: main_krylov, s5:moment(b).
Proof: the actual normalized positive spectral data supplies the proved weighted-Dirac instance. -/
instance gradientProbabilityMeasure_probability (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (hg : g≠0) :
    IsProbabilityMeasure (gradientProbabilityMeasure A hA g hg) :=
  discreteAtomicMeasure_probability _

/-- Every moment of the actual physical spectral probability measure is the
original gradient spectral moment used in the source's information data.
Use: no finite-sum/genuine-measure discrepancy enters the attainment theorem.
Article: main_krylov, s5:moment(b).
Proof: evaluate the real monomial using the proved actual weighted-Dirac integral identity. -/
theorem gradient_probability_moment (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (hg : g≠0) (k : ℕ) :
    measureMoment (gradientProbabilityMeasure A hA g hg) k=gradientMoment A hA g hg k :=
  discrete_atomic_integral (gradientSpectralData A hA g hg) (fun x => x^k)

/-- Original physical spectral-band forms imply almost everywhere support
of the actual normalized gradient probability measure in that closed band.
Use: every genuine physical Radau completion supplies a truly supported measure.
Article: main_krylov, s5:moment(b).
Proof: original orthogonal spectral coordinates put each real eigenvalue in
the physical interval; each actual gradient atom is one of those eigenvalues,
and the constructed genuine probability measure is supported on its actual nodes. -/
theorem gradient_probability_supported (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (hg : g≠0) (mu upper : ℝ)
    (hlo : (A-mu • 1).PosSemidef) (hhi : (upper • 1-A).PosSemidef) :
    ∀ᵐ x ∂gradientProbabilityMeasure A hA g hg,x∈Set.Icc mu upper := by
  let B := chebyshev1.SpectralBasis.ofHermitian A hA.1
  have hl := (coordinates_posSemidef_iff B (A-mu • 1)).mpr hlo
  have hh := (coordinates_posSemidef_iff B (upper • 1-A)).mpr hhi
  have he : A-mu • 1=(-mu) • 1+A := by module
  rw [he,coordinates_lower_shift,Matrix.posSemidef_diagonal_iff] at hl
  rw [coordinates_upper_shift,Matrix.posSemidef_diagonal_iff] at hh
  apply discrete_atomic_supported
  intro i
  obtain ⟨j,hj⟩ := gradientSpectralData_node_eigenvalue A hA g hg i
  rw [← hj]
  change mu≤hA.1.eigenvalues j ∧ hA.1.eigenvalues j≤upper
  have hl' : 0≤-mu+hA.1.eigenvalues j := hl j
  have hh' : 0≤upper-hA.1.eigenvalues j := hh j
  constructor <;> linarith

/-- Every actual admissible physical pivot has a genuine supported probability
measure realizing all original known moments and its exact printed missing moment.
Use: every point, including both endpoints and a collapsed interval, is attained
in the original all-probability-measure problem.
Article: main_krylov, s5:moment(b), reverse attainment.
Proof: construct the actual completion's real gradient spectral probability
measure; true physical spectral bounds give support, while the original
information-fibre fixed and affine missing-moment theorems give its exact moments. -/
theorem spectral_moment_attainment
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (I : chebyshev1.SpectralInterval)
    (hne : ∃ b : ℝ,(lanczosCompletion A hA g hg hc b-I.mu • 1).PosSemidef ∧
      (I.L • 1-lanczosCompletion A hA g hg hc b).PosSemidef)
    (b : ℝ) (hb : b∈Set.Icc (spectralLowerPivot A hA g hg hc I.mu) (spectralUpperPivot A hA g hg hc I.L)) :
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    ∃ sigma : Measure ℝ,IsProbabilityMeasure sigma ∧
      (∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L) ∧
      (∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k) ∧
      measureMoment sigma (2*n+1)=c*b+(gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc) := by
  have hinterval := physical_spectral_fibre_interval A hA g hg hc I.mu I.L hne
  have hband := (hinterval.2 b).mpr hb
  let C := lanczosCompletion A hA g hg hc b
  have hC : C.PosDef := spectral_fibre_completion_positive A hA g hg hc I.mu b I.mu_pos hband.1
  refine ⟨gradientProbabilityMeasure C hC g hg,inferInstance,
    gradient_probability_supported C hC g hg I.mu I.L hband.1 hband.2,?_,?_⟩
  · intro k hk
    rw [gradient_probability_moment]
    exact fibre_fixed_gradient_moments A hA g hg hc b hC k hk
  · rw [gradient_probability_moment]
    exact fibre_missing_gradient_moment A hA g hg hc b hC

end
end krylov.OneGradient

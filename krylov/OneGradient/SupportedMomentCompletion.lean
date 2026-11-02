import krylov.OneGradient.MomentCompression
import krylov.OneGradient.SpectralFibreParameters
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), arbitrary supported probability measures.
Use: derive a genuine physical spectral completion from the actual moments
of every probability measure supported on the original spectral interval.
Source: the reused actual compact-measure polynomial integral and localizing
square positivity, actual moment-derived Gram identity and original physical
closed Jacobi spectral completion theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix MeasureTheory krylov.Reference
variable {n : ℕ}

/-- Any actual polynomial integral with the original known moments and genuine
endpoint localizing-square positivity constructs an actual physical spectral completion.
Use: the all-measures moment problem is reduced by a derived real matrix,
without assuming a candidate measure has any Jacobi representation.
Article: main_krylov, s5:moment(b).
Proof: known moments derive the true orthonormal Gram identity. Both nonnegative
localizing square forms are therefore the actual shifted multiplication matrices;
the original true orthogonal Lanczos coordinates transport them to the physical completion. -/
theorem moment_completion_spectral
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (F : ℝ[X] →ₗ[ℝ] ℝ) (hm : ∀ k≤2*n,F (X^k)=gradientMoment A hA g hg k)
    (mu upper : ℝ) (hlo : ∀ p : ℝ[X],0≤F ((X-C mu)*p^2))
    (hhi : ∀ p : ℝ[X],0≤F ((C upper-X)*p^2)) :
    let q := physicalLanczosPolynomials A hA g hg hc
    let b := F (X*q (Fin.last n)*q (Fin.last n))
    (lanczosCompletion A hA g hg hc b-mu • 1).PosSemidef ∧
      (upper • 1-lanczosCompletion A hA g hg hc b).PosSemidef := by
  let q := physicalLanczosPolynomials A hA g hg hc
  let b := F (X*q (Fin.last n)*q (Fin.last n))
  let Z := physicalLanczosColumns A hA g hg hc
  let P := lanczosCompletion A hA g hg hc b
  let T := polynomialForm F q X
  have hGram : polynomialForm F q 1=1 := moment_polynomial_gram A hA g hg hc F hm
  have hcomp : T=Zᵀ*P*Z := moment_multiplication_completion A hA g hg hc F hm
  have hZ : Zᵀ*Z=1 := physical_lanczos_orthogonal A hA g hg hc
  have hl : polynomialForm F q (X-C mu)=T-mu • 1 := by
    rw [polynomial_form_sub,polynomial_form_constant,hGram]
  have hh : polynomialForm F q (C upper-X)=upper • 1-T := by
    rw [polynomial_form_sub,polynomial_form_constant,hGram]
  have hTL : (T-mu • 1).PosSemidef := hl ▸ polynomial_form_positive F q (X-C mu) hlo
  have hTH : (upper • 1-T).PosSemidef := hh ▸ polynomial_form_positive F q (C upper-X) hhi
  dsimp only
  constructor
  · apply (physical_lanczos_positive_iff A hA g hg hc _).mp
    change (Zᵀ*(P-mu • 1)*Z).PosSemidef
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hZ]
    rw [← hcomp]
    exact hTL
  · apply (physical_lanczos_positive_iff A hA g hg hc _).mp
    change (Zᵀ*(upper • 1-P)*Z).PosSemidef
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hZ]
    rw [← hcomp]
    exact hTH

/-- The actual kth moment of any genuine real probability measure.
Use: the missing-moment interval quantifies over arbitrary measures, including
non-atomic and singular continuous measures on the spectral interval.
Article: main_krylov, s5:moment(b). -/
def measureMoment (sigma : Measure ℝ) (k : ℕ) : ℝ := ∫ x,x^k ∂sigma

/-- Every supported probability measure with the actual observed moments
has its genuine last multiplication integral inside the original physical
closed Gauss--Radau pivot interval.
Use: this direction covers all probability measures, not just atomic candidates.
Article: main_krylov, s5:moment(b).
Proof: actual compact support derives genuine polynomial integrability and
both localizing-square inequalities. Actual low moments derive its polynomial
Gram; the constructed real physical completion is in the spectral band and
hence in the proved original closed spectral information interval. -/
theorem supported_measure_completion_interval
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma] (I : chebyshev1.SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k) :
    let F := measurePolynomialIntegral sigma I hI
    let q := physicalLanczosPolynomials A hA g hg hc
    F (X*q (Fin.last n)*q (Fin.last n))∈
      Set.Icc (spectralLowerPivot A hA g hg hc I.mu) (spectralUpperPivot A hA g hg hc I.L) := by
  let F := measurePolynomialIntegral sigma I hI
  let q := physicalLanczosPolynomials A hA g hg hc
  let b := F (X*q (Fin.last n)*q (Fin.last n))
  have hF (k : ℕ) (hk : k≤2*n) : F (X^k)=gradientMoment A hA g hg k := by
    simpa only [F,measurePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,eval_pow,eval_X,measureMoment] using hm k hk
  have hband := moment_completion_spectral A hA g hg hc F hF I.mu I.L
    (measurePolynomialIntegral_lower sigma I hI) (measurePolynomialIntegral_upper sigma I hI)
  have hinterval := physical_spectral_fibre_interval A hA g hg hc I.mu I.L ⟨b,hband⟩
  exact (hinterval.2 b).mp hband

end
end krylov.OneGradient

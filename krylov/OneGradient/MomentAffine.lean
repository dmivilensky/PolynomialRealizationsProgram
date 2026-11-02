import krylov.OneGradient.SupportedMomentCompletion
import krylov.OneGradient.TopMoment
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), missing moment of arbitrary probability measures.
Use: derive the exact original missing-moment affine formula for every genuine
supported measure with the observed moment sequence, including non-atomic measures.
Source: genuine low-degree polynomial moment comparison, actual leading-monomial
removal and the original positive Jacobi coupling-product normalization.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix MeasureTheory krylov.Reference jacobi.Finite
variable {n : ℕ}

/-- The actual last polynomial multiplication integral of the original gradient
measure is its genuine final physical Jacobi diagonal.
Use: fix the affine missing-moment constant from the original physical reference.
Article: main_krylov, s5:moment(b).
Proof: the actual finite polynomial integral is its weighted-evaluation pairing;
the reused genuine Lanczos compression identifies its final multiplication entry. -/
theorem original_polynomial_last_curvature
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) :
    let q := physicalLanczosPolynomials A hA g hg hc (Fin.last n)
    discretePolynomialIntegral (gradientSpectralData A hA g hg) (X*q*q)=lastJacobiPivot A hA g hg hc := by
  let M := gradientSpectralData A hA g hg
  let j : Fin (activeSpectralValues A hA.1 g).card := ⟨n,by rw [hc];omega⟩
  let q := physicalLanczosPolynomials A hA g hg hc (Fin.last n)
  have hp : X*q*q=q*(X*q) := by ring
  dsimp only
  change discretePolynomialIntegral M (X*q*q)=_
  rw [hp,discrete_integral_product]
  change inner ℝ (M.evaluate (M.orthogonalPolynomial j)) (M.evaluate (X*M.orthogonalPolynomial j))=_
  rw [M.evaluate_orthogonalPolynomial]
  change M.multiplication j j=_
  rw [← M.reconstructed_matrix]
  exact (lanczosVector_compression A hA g hg j j).symm

/-- The first unknown moment of any actual polynomial integral sharing the
original known moments has the printed physical Jacobi affine formula.
Use: the all-measures coefficient is the same actual positive coupling-product
square as for the original constructed physical completions.
Article: main_krylov, s5:moment(b).
Proof: remove the leading monomial from X times the actual last orthogonal
polynomial square. Its lower part is fixed by the observed moments, and its
genuine leading coefficient is the inverse coupling-product square. -/
theorem arbitrary_integral_missing_moment
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (F : ℝ[X] →ₗ[ℝ] ℝ) (hm : ∀ k≤2*n,F (X^k)=gradientMoment A hA g hg k) :
    let q := physicalLanczosPolynomials A hA g hg hc (Fin.last n)
    let b := F (X*q*q)
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    F (X^(2*n+1))=c*b+(gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc) := by
  let M := gradientSpectralData A hA g hg
  let G := discretePolynomialIntegral M
  let j : Fin (activeSpectralValues A hA.1 g).card := ⟨n,by rw [hc];omega⟩
  let q := physicalLanczosPolynomials A hA g hg hc (Fin.last n)
  let p := X*q*q
  let L := M.reconstructed.data.linkProduct n
  have hL : 0<L := linkProduct_pos M.reconstructed_irreducible j.isLt
  have hqdeg : q.natDegree=n := physical_polynomial_degree A hA g hg hc (Fin.last n)
  have hqlc : q.leadingCoeff=L⁻¹ := spectral_polynomial_leadingCoeff M j
  have hq0 : q≠0 := by
    apply leadingCoeff_ne_zero.mp
    rw [hqlc]
    exact inv_ne_zero hL.ne'
  have hpdeg : p.natDegree=2*n+1 := by
    dsimp only [p]
    rw [natDegree_mul (mul_ne_zero X_ne_zero hq0) hq0,natDegree_mul X_ne_zero hq0,natDegree_X,hqdeg]
    omega
  have hplc : p.leadingCoeff=(L⁻¹)^2 := by
    dsimp only [p]
    rw [leadingCoeff_mul,leadingCoeff_mul,leadingCoeff_X,one_mul,hqlc]
    ring
  have hmatch (k : ℕ) (hk : k≤2*n) : F (X^k)=G (X^k) :=
    (hm k hk).trans (discrete_gradient_moment A hA g hg k).symm
  have he := top_moment_difference F G (2*n) hmatch p hpdeg
  have hGp : G p=lastJacobiPivot A hA g hg hc := original_polynomial_last_curvature A hA g hg hc
  have hGk : G (X^(2*n+1))=gradientMoment A hA g hg (2*n+1) := discrete_gradient_moment A hA g hg _
  rw [hGp,hplc,hGk] at he
  have hscale : L^2*(L⁻¹)^2=1 := by field_simp
  have he' := congrArg (fun t : ℝ => L^2*t) he
  simp only [← mul_assoc,hscale,one_mul] at he'
  dsimp only
  change F (X^(2*n+1))=L^2*F p+(gradientMoment A hA g hg (2*n+1)-L^2*lastJacobiPivot A hA g hg hc)
  nlinarith

/-- Every genuine supported probability measure with the source's known
moments has its first missing moment in the exact affine image of the actual
physical Gauss--Radau pivot interval.
Use: the inclusion quantifies over all probability measures without a finite
support or preassigned Jacobi-representation assumption.
Article: main_krylov, s5:moment(b), all-measures inclusion.
Proof: actual support gives the derived physical completion interval; true
leading-monomial comparison gives the identical printed affine moment formula. -/
theorem supported_measure_missing_moment
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (sigma : Measure ℝ) [IsProbabilityMeasure sigma] (I : chebyshev1.SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (hm : ∀ k≤2*n,measureMoment sigma k=gradientMoment A hA g hg k) :
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    ∃ b∈Set.Icc (spectralLowerPivot A hA g hg hc I.mu) (spectralUpperPivot A hA g hg hc I.L),
      measureMoment sigma (2*n+1)=c*b+(gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc) := by
  let F := measurePolynomialIntegral sigma I hI
  let q := physicalLanczosPolynomials A hA g hg hc (Fin.last n)
  let b := F (X*q*q)
  have hF (k : ℕ) (hk : k≤2*n) : F (X^k)=gradientMoment A hA g hg k := by
    simpa only [F,measurePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,eval_pow,eval_X,measureMoment] using hm k hk
  refine ⟨b,supported_measure_completion_interval A hA g hg hc sigma I hI hm,?_⟩
  have he := arbitrary_integral_missing_moment A hA g hg hc F hF
  dsimp only at he
  have hFK : F (X^(2*n+1))=measureMoment sigma (2*n+1) := by
    simp only [F,measurePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,eval_pow,eval_X,measureMoment]
  rw [hFK] at he
  exact he

end
end krylov.OneGradient

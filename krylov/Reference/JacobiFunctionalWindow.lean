import krylov.Reference.JacobiFunctionalGauss
import krylov.Reference.JacobiTruncation
import krylov.Reference.CompactMeasureIntegral
import krylov.LinearAlgebra.PositiveGaussNodes
import krylov.LinearAlgebra.NormOrder
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), Gaussian support derived from the original spectral measure.
Use: discharge the genuine finite Gauss matrix window from original probability support and actual Jacobi recurrence orthogonality.
Source: the proved Gaussian polynomial exactness, genuine positive first-site weights and cardinal-square support argument.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial chebyshev1 krylov.LinearAlgebra
open scoped BigOperators

/-- Every actual finite Jacobi quadrature node lies in the original functional support window derived from its genuine localizing square inequalities.
Use: Every actual finite Jacobi quadrature node lies in the original functional support window derived from its genuine localizing square inequalities.
Article: main_krylov, prop:phi(c), Gaussian support derived from the original spectral measure.
Proof: The original Gaussian exactness and true positive spectral weights isolate each real node by its actual cardinal square. -/
theorem jacobiFunctional_node_window (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (F : ℝ[X] →ₗ[ℝ] ℝ) (h1 : F 1=1)
    (ho : ∀ m q,q.natDegree<m → F (J.leading m*q)=0) (mu L : ℝ)
    (hlo : ∀ q : ℝ[X],0≤F ((X-C mu)*q^2))
    (hup : ∀ q : ℝ[X],0≤F ((C L-X)*q^2)) (N : ℕ) :
    let S := SpectralBasis.ofHermitian (J.matrix 0 N) (J.matrix_isHermitian 0 N)
    ∀ j,mu≤S.eigenvalues j ∧ S.eigenvalues j≤L := by
  -- Isolate each true positive spectral weight by genuine original Gaussian exactness.
  dsimp only
  cases N with
  | zero => intro j;exact Fin.elim0 j
  | succ n =>
    let S := SpectralBasis.ofHermitian (J.matrix 0 (n+1)) (J.matrix_isHermitian 0 (n+1))
    have hi := jacobiData_values_injective J hJ hpos (n+1) S
    have hw (j : Fin (n+1)) : 0<S.weight 0 j :=
      (J.spectral_endpoint_positive S hJ (fun s hs _ => hpos s hs) hi j).1
    have hg (p : ℝ[X]) (hp : p.natDegree<2*(n+1)) :
        (∑ j,S.weight 0 j*p.eval (S.eigenvalues j))=F p := by
      have he := jacobiFunctional_spectral J (n+1) (by omega) p
      have heq : jacobiFunctional J (n+1) (by omega) p=(∑ j,S.weight 0 j*p.eval (S.eigenvalues j)) := he
      rw [← heq]
      exact jacobiFunctional_gauss_exact J hJ F h1 ho (by omega) hp
    intro j
    have hl := finite_gauss_nonnegative_node S.eigenvalues (S.weight 0) hi hw F hg
      (X-C mu) (natDegree_X_sub_C_le mu) hlo j
    have hu := finite_gauss_nonnegative_node S.eigenvalues (S.weight 0) hi hw F hg
      (C L-X) (by compute_degree) hup j
    simpa only [eval_sub,eval_X,eval_C,sub_nonneg] using And.intro hl hu

/-- Every actual Gauss Jacobi block of the original compactly supported probability measure satisfies both genuine physical spectral forms.
Use: Every actual Gauss Jacobi block of the original compactly supported probability measure satisfies both genuine physical spectral forms.
Article: main_krylov, prop:phi(c), Gaussian support derived from the original spectral measure.
Proof: Derive actual node bounds from original integral positivity, then use the actual orthogonal spectral coordinates to recover the physical forms. -/
theorem jacobiMeasure_window (J : JacobiData) (hJ : ∀ n,0≤J.aSq n)
    (hpos : ∀ n,0<n → 0<J.aSq n) (sigma : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure sigma] (I : SpectralInterval)
    (hI : ∀ᵐ x ∂sigma,x∈Set.Icc I.mu I.L)
    (ho : ∀ m q,q.natDegree<m → measurePolynomialIntegral sigma I hI (J.leading m*q)=0)
    (N : ℕ) : (J.matrix 0 N-I.mu • 1).PosSemidef ∧
      (I.L • (1 : Matrix (Fin N) (Fin N) ℝ)-J.matrix 0 N).PosSemidef := by
  -- Derive the actual physical matrix window from original support, rather than assuming the desired finite spectral bounds.
  let S := SpectralBasis.ofHermitian (J.matrix 0 N) (J.matrix_isHermitian 0 N)
  have hw := jacobiFunctional_node_window J hJ hpos (measurePolynomialIntegral sigma I hI)
    (measurePolynomialIntegral_one sigma I hI) ho I.mu I.L
    (measurePolynomialIntegral_lower sigma I hI) (measurePolynomialIntegral_upper sigma I hI) N
  constructor
  · have he : J.matrix 0 N-I.mu • 1=(-I.mu) • (1 : Matrix (Fin N) (Fin N) ℝ)+J.matrix 0 N := by module
    rw [he,← coordinates_posSemidef_iff S,coordinates_lower_shift,Matrix.posSemidef_diagonal_iff]
    intro i
    linarith [(hw i).1]
  · rw [← coordinates_posSemidef_iff S,coordinates_upper_shift,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (hw i).2
end
end krylov.Reference

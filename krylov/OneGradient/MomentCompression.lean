import krylov.OneGradient.PolynomialMoments
import krylov.OneGradient.JacobiCoordinates
import krylov.OneGradient.FibreMoments
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(b), real multiplication compression from moment data.
Use: construct the genuine Jacobi completion associated with any actual
polynomial integral sharing the original observed moments.
Source: actual gradient orthogonal polynomials, exact low-moment polynomial
comparison and the genuine polynomial-square compression formula.
-/

namespace krylov.OneGradient
noncomputable section
open Polynomial Matrix krylov.Reference jacobi.Finite
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- The actual original gradient measure's orthogonal polynomials, reindexed
by the original full physical dimension.
Use: arbitrary measures are tested against the actual reference's polynomial
basis, without assuming that their own Jacobi reconstruction is known.
Article: main_krylov, s5:moment(b). -/
def physicalLanczosPolynomials
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (i : Fin (n+1)) : ℝ[X] :=
  (gradientSpectralData A hA g hg).orthogonalPolynomial ⟨i.val,by rw [hc];exact i.isLt⟩

/-- The actual original spectral polynomials retain exactly their real indexed degree.
Use: all polynomial identities transferred to an arbitrary measure lie within
the original explicitly known moment orders.
Article: main_krylov, s5:moment(b).
Proof: the actual constructed spectral orthogonal family has its proved degree. -/
theorem physical_polynomial_degree
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (i : Fin (n+1)) :
    (physicalLanczosPolynomials A hA g hg hc i).natDegree=i.val :=
  ((gradientSpectralData A hA g hg).orthogonalPolynomial_degree _).1

/-- The actual spectral polynomial integral of every monomial is the original
physical gradient spectral moment.
Use: the source's original numerical moments directly supply polynomial-functional equality.
Article: main_krylov, s5:moment(b).
Proof: evaluate the real monomial at each genuine positive spectral atom. -/
theorem discrete_gradient_moment
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0) (k : ℕ) :
    discretePolynomialIntegral (gradientSpectralData A hA g hg) (X^k)=gradientMoment A hA g hg k := by
  simp only [discretePolynomialIntegral,LinearMap.coe_mk,AddHom.coe_mk,gradientMoment,eval_pow,eval_X]

/-- Any real polynomial integral with the actual known physical moments has
the original orthonormal polynomial Gram equal to the actual identity matrix.
Use: no orthogonality of an arbitrary candidate probability measure is assumed.
Article: main_krylov, s5:moment(b).
Proof: each genuine product has degree at most 2n. The original observed moments
therefore transfer its actual finite spectral Gram, already proved orthonormal. -/
theorem moment_polynomial_gram
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (F : ℝ[X] →ₗ[ℝ] ℝ) (hm : ∀ k≤2*n,F (X^k)=gradientMoment A hA g hg k) :
    polynomialForm F (physicalLanczosPolynomials A hA g hg hc) 1=1 := by
  let M := gradientSpectralData A hA g hg
  let q := physicalLanczosPolynomials A hA g hg hc
  have hmatch (p : ℝ[X]) (hp : p.natDegree≤2*n) : F p=discretePolynomialIntegral M p :=
    polynomial_integrals_eq_of_moments F _ (2*n) (fun k hk => (hm k hk).trans (discrete_gradient_moment A hA g hg k).symm) p hp
  ext i j
  change F (1*q i*q j)=(1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j
  rw [one_mul,hmatch _ (by
    apply Polynomial.natDegree_mul_le.trans
    rw [physical_polynomial_degree,physical_polynomial_degree]
    omega),discrete_integral_product]
  dsimp only [q,physicalLanczosPolynomials]
  rw [M.evaluate_orthogonalPolynomial,M.evaluate_orthogonalPolynomial,M.polynomialBasis.inner_eq_ite]
  simp only [Matrix.one_apply,Fin.mk.injEq,Fin.val_inj]

/-- Every candidate polynomial integral's multiplication matrix equals the
actual original physical Jacobi completion with its true last integral as pivot.
Use: realize the entire all-probability-measure moment constraint as an actual
finite Jacobi compression rather than postulate a missing-moment completion field.
Article: main_krylov, s5:moment(b).
Proof: all entries except last-last involve only moments through 2n, so genuine
known-moment equality identifies their actual physical Jacobi entries. The last
entry is the actual integral of X times the last polynomial square. -/
theorem moment_multiplication_completion
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (F : ℝ[X] →ₗ[ℝ] ℝ) (hm : ∀ k≤2*n,F (X^k)=gradientMoment A hA g hg k) :
    let q := physicalLanczosPolynomials A hA g hg hc
    let b := F (X*q (Fin.last n)*q (Fin.last n))
    polynomialForm F q X=(physicalLanczosColumns A hA g hg hc)ᵀ*lanczosCompletion A hA g hg hc b*
      physicalLanczosColumns A hA g hg hc := by
  let M := gradientSpectralData A hA g hg
  let q := physicalLanczosPolynomials A hA g hg hc
  have hmatch (p : ℝ[X]) (hp : p.natDegree≤2*n) : F p=discretePolynomialIntegral M p :=
    polynomial_integrals_eq_of_moments F _ (2*n) (fun k hk => (hm k hk).trans (discrete_gradient_moment A hA g hg k).symm) p hp
  dsimp only
  ext i j
  rw [physical_lanczos_completion]
  by_cases hlast : i=Fin.last n ∧ j=Fin.last n
  · obtain ⟨rfl,rfl⟩ := hlast
    simp [polynomialForm]
  · rw [ite_eq_right hlast]
    change F (X*q i*q j)=_
    have hdegree : (X*q i*q j).natDegree≤2*n := by
      apply Polynomial.natDegree_mul_le.trans
      apply Nat.add_le_add_right (Polynomial.natDegree_mul_le) _ |>.trans
      rw [Polynomial.natDegree_X,physical_polynomial_degree,physical_polynomial_degree]
      have hi : i.val≤n := by omega
      have hj : j.val≤n := by omega
      have hnot : ¬(i.val=n ∧ j.val=n) := by
        rintro ⟨hi',hj'⟩
        exact hlast ⟨Fin.ext hi',Fin.ext hj'⟩
      omega
    rw [hmatch _ hdegree,physical_lanczos_jacobi,M.reconstructed_matrix]
    have hpoly : X*q i*q j=q i*(X*q j) := by ring
    rw [hpoly,discrete_integral_product]
    dsimp only [q,physicalLanczosPolynomials]
    rw [M.evaluate_orthogonalPolynomial]
    rfl

end
end krylov.OneGradient

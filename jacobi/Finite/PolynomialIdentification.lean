import jacobi.Finite.Fiber
import Mathlib.Algebra.Polynomial.RingDivision

/-!
Article: jacobi, Proposition 6.1.
The original node product is identified with a proposed classical
polynomial by actual monicity, degree and every genuine root. Its
positive affine change has the exact full polynomial normalization.
Source: coprime linear-factor divisibility and monic polynomial uniqueness.
Use: eq_polynomial identifies the source's classical terminal polynomials with their complete original node fibres.
-/
namespace jacobi.Finite.Nodes
noncomputable section
open Polynomial
open scoped BigOperators

/-- The full original node polynomial is monic.
Use: eq_polynomial identifies the source's classical terminal polynomials with their complete original node fibres.
Article: jacobi, Proposition 6.1.
Proof: the finite product of the actual monic linear factors is monic. -/
theorem monic {N:ℕ} (S: jacobi.Finite.Nodes N) : S.polynomial.Monic :=
  monic_prod_X_sub_C S.value Finset.univ

/-- The original node polynomial has exactly its genuine matrix dimension as degree.
Use: eq_polynomial excludes an extra classical factor after all original finite nodes have been identified.
Article: jacobi, Proposition 6.1.
Proof: add the degree one of every original monic linear factor in the full finite node product. -/
theorem natDegree {N:ℕ} (S: jacobi.Finite.Nodes N) : S.polynomial.natDegree=N := by
  simp only [jacobi.Finite.Nodes.polynomial,
    natDegree_prod_of_monic Finset.univ (fun i=>X-C (S.value i))
      (fun i _=>monic_X_sub_C (S.value i)),natDegree_X_sub_C,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

/-- A genuine monic polynomial of the original degree with all original prescribed nodes is exactly the complete source node polynomial.
Use: the actual U polynomial and its positive affine image have precisely the original complete finite fibres.
Article: jacobi, Proposition 6.1.
Proof: distinct actual nodes give pairwise coprime linear factors.
They all divide the proposed polynomial, so their full monic product
divides it. Equal original degree and monicity force actual equality. -/
theorem eq_polynomial {N:ℕ} (S: jacobi.Finite.Nodes N) {p:Polynomial ℝ} (hp:p.Monic)
    (hdeg:p.natDegree=N) (hroot:∀i,p.eval (S.value i)=0) : p=S.polynomial := by
  classical
  -- Divisibility uses every genuine finite node, rather than only equality of a limiting spectral set.
  have hd:S.polynomial∣p :=
    Finset.prod_dvd_of_coprime
      (fun i _ j _ hij=>pairwise_coprime_X_sub_C S.strictAnti.injective hij)
      (fun i _=>dvd_iff_isRoot.mpr (hroot i))
  exact eq_of_monic_of_dvd_of_natDegree_le S.monic hp hd (by rw [hdeg,S.natDegree])

/-- The actual full affine node polynomial has its exact original degree-power factor and spectral substitution.
Use: the U counterexample polynomial is literally (theta/2)^n*U_n((x-1+theta)/theta), with no missing scalar normalization.
Article: jacobi, Proposition 6.1.
Proof: factor theta from each genuine original linear factor and
multiply all N factors, including the empty original product. -/
theorem affine_eval {N:ℕ} (S T: jacobi.Finite.Nodes N) {theta d:ℝ} (ht:theta≠0)
    (hnode:∀i,T.value i=theta*S.value i+d) (x:ℝ) :
    T.polynomial.eval x=theta^N*S.polynomial.eval ((x-d)/theta) := by
  classical
  -- The identity concerns the complete original polynomial, before any asymptotic limit.
  simp only [jacobi.Finite.Nodes.polynomial,eval_prod,eval_sub,eval_X,eval_C,hnode]
  calc
    _ = ∏i:Fin N,theta*((x-d)/theta-S.value i) := by
      apply Finset.prod_congr rfl
      intro i _
      field_simp
      ring
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

end
end jacobi.Finite.Nodes

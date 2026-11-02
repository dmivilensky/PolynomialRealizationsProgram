import krylov.Reference.Christoffel
import jacobi.Finite.NormalizedPolynomials
import Mathlib.Algebra.Polynomial.Sequence

/-!
Article: main_krylov, Section 3 introductory Gauss interpretation of the CG error.
Use: prove polynomial exactness of the actual leading Jacobi quadrature,
reusing the earlier continuants, spectral calculus and reconstructed measure.
Source: the classical Gaussian quadrature division proof (Golub73,
Gautschi02, GolubMeurant10). No quadrature exactness is a structure field.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite chebyshev1 chebyshev2
open scoped BigOperators InnerProductSpace

/-- Polynomial integration against the actual finite probability measure.
Use: states quadrature exactness as an equality of genuine linear functionals.
Article: main_krylov, lem:chris, polynomial spectral integration. -/
def polynomialIntegral {N : ℕ} (M : DiscreteMeasure N) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∑ i, M.weight i*p.eval (M.node i)
  map_add' p q := by simp only [eval_add, mul_add, Finset.sum_add_distrib]
  map_smul' a p := by simp only [eval_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]; congr 1; funext i; ring

/-- The first-site polynomial functional of an actual finite Jacobi block.
Use: its spectral representation is the constructed Gaussian quadrature rule.
Article: main_krylov, Section 3, the l-point Gauss rule. -/
def jacobiFunctional (J : JacobiData) (m : ℕ) (hm : 0<m) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := (aeval (J.matrix 0 m) p) ⟨0, hm⟩ ⟨0, hm⟩
  map_add' p q := by simp only [map_add, Matrix.add_apply]
  map_smul' a p := by simp only [map_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- The actual Jacobi functional has its genuine finite spectral quadrature representation.
Use: identifies the nodes and nonnegative weights of the constructed rule.
Article: main_krylov, Section 3, Gaussian spectral quadrature.
Proof: reuse the already proved first-site spectral moment theorem. -/
theorem jacobiFunctional_spectral (J : JacobiData)
    (m : ℕ) (hm : 0<m) (p : ℝ[X]) :
    jacobiFunctional J m hm p=
      ∑ i : Fin m, (SpectralBasis.ofHermitian (J.matrix 0 m) (J.matrix_isHermitian 0 m)).weight ⟨0, hm⟩ i*
        p.eval ((SpectralBasis.ofHermitian (J.matrix 0 m) (J.matrix_isHermitian 0 m)).eigenvalues i) := by
  exact SpectralBasis.moment p (J.matrix_isHermitian 0 m) ⟨0, hm⟩

/-- Every leading block has the same first-site functional on an earlier continuant.
Use: the low-degree moment comparison is inherited from the existing leading-site identity.
Article: main_krylov, Section 3, Gaussian moment matching.
Proof: apply the already proved continuant operator identity to the first coordinate vector. -/
theorem jacobiFunctional_leading (J : JacobiData) (hJ : ∀ i, 0≤J.aSq i)
    (m : ℕ) (hm : 0<m) {k : ℕ} (hk : k<m) :
    jacobiFunctional J m hm (J.leading k)=J.linkProduct k*(if k=0 then 1 else 0) := by
  have he := J.leading_aeval_site m k hm hk hJ
  rw [JacobiData.site_eq_single m 0 hm, Matrix.mulVec_single_one] at he
  have hc := congrFun he ⟨0, hm⟩
  change (aeval (J.matrix 0 m) (J.leading k)) ⟨0, hm⟩ ⟨0, hm⟩=_
  simpa only [Pi.smul_apply, smul_eq_mul, JacobiData.site, Fin.val_mk, eq_comm, Matrix.col_apply] using hc

/-- Existing monic continuants form a degree-graded polynomial sequence.
Use: reuses mathlib's full low-degree spanning theorem in the quadrature proof.
Article: main_krylov, Section 3, leading Jacobi polynomials. -/
def leadingSequence (J : JacobiData) (hJ : ∀ i, 0≤J.aSq i) : Polynomial.Sequence ℝ where
  elems' := J.leading
  degree_eq' i := by
    rw [JacobiData.leading, degree_eq_natDegree (J.block_monic hJ 0 i).ne_zero,
      J.block_natDegree hJ 0 i]

/-- First-site Jacobi polynomial moments of degree below m are fixed by the leading m-site block.
Use: starts Gaussian exactness without a path-counting assumption.
Article: main_krylov, Section 3 and s5:fibre, observed low-degree moments.
Proof: the existing continuants span the full low-degree polynomial space,
and their first-site values are independent of the larger block size. -/
theorem jacobiFunctional_low_degree (J : JacobiData) (hJ : ∀ i, 0≤J.aSq i)
    {m N : ℕ} (hm : 0<m) (hmN : m≤N) {p : ℝ[X]} (hp : p.degree<m) :
    jacobiFunctional J m hm p=jacobiFunctional J N (hm.trans_le hmN) p := by
  -- Equality on a genuine polynomial basis extends to the full admissible linear space.
  let S := leadingSequence J hJ
  have hspan := S.span_degreeLT (m := m) (fun i _ => isUnit_iff_ne_zero.mpr
    (leadingCoeff_ne_zero.mpr (S.ne_zero i)))
  have hle : Submodule.span ℝ (S '' Set.Iio m)≤
      (jacobiFunctional J m hm-jacobiFunctional J N (hm.trans_le hmN)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change jacobiFunctional J m hm (J.leading i)-jacobiFunctional J N (hm.trans_le hmN) (J.leading i)=0
    rw [jacobiFunctional_leading J hJ m hm hi,
      jacobiFunctional_leading J hJ N (hm.trans_le hmN) (hi.trans_le hmN), sub_self]
  apply sub_eq_zero.mp
  apply hle
  rw [hspan, mem_degreeLT]
  exact hp

/-- Polynomial integration in the input measure is the first-site functional of its actually reconstructed Jacobi matrix.
Use: connects the reused inverse spectral construction to Gaussian quadrature of the prescribed measure.
Article: main_krylov, Section 3, measure/Jacobi dictionary.
Proof: the actual spectral coordinates diagonalize the polynomial matrix;
the reconstructed first row is the square root of the prescribed weights. -/
theorem polynomialIntegral_reconstructed {N : ℕ} (M : DiscreteMeasure N) (p : ℝ[X]) :
    polynomialIntegral M p=jacobiFunctional M.reconstructed.data N (support_pos M) p := by
  -- Recover the polynomial matrix from its genuine constructed spectral basis, rather than changing spectral weights.
  have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => M.reconstructedBasis.Q*A*M.reconstructedBasis.Qᵀ)
    (spectral_coordinates_aeval M.reconstructedBasis p)
  have hmat : aeval M.reconstructed.matrix p=M.reconstructedBasis.Q*
      Matrix.diagonal (fun i => p.eval (M.node i))*M.reconstructedBasis.Qᵀ := by
    change M.reconstructedBasis.Q*(M.reconstructedBasis.Qᵀ*aeval M.reconstructed.matrix p*M.reconstructedBasis.Q)*
      M.reconstructedBasis.Qᵀ=_ at he
    have hleft : M.reconstructedBasis.Q*(M.reconstructedBasis.Qᵀ*aeval M.reconstructed.matrix p*M.reconstructedBasis.Q)*
        M.reconstructedBasis.Qᵀ=aeval M.reconstructed.matrix p := by
      calc
        _ = (M.reconstructedBasis.Q*M.reconstructedBasis.Qᵀ)*aeval M.reconstructed.matrix p*
            (M.reconstructedBasis.Q*M.reconstructedBasis.Qᵀ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [M.reconstructedBasis.mul_transpose, Matrix.one_mul, Matrix.mul_one]
    exact hleft.symm.trans he
  change _=(aeval M.reconstructed.matrix p) ⟨0, support_pos M⟩ ⟨0, support_pos M⟩
  rw [hmat, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  change (∑ i, M.weight i*p.eval (M.node i))=_
  apply Finset.sum_congr rfl
  intro i _
  change M.weight i*p.eval (M.node i)=
    M.eigenvectors ⟨0, support_pos M⟩ i*p.eval (M.node i)*M.eigenvectors ⟨0, support_pos M⟩ i
  rw [M.eigenvectors_first]
  calc
    _ = (Real.sqrt (M.weight i))^2*p.eval (M.node i) := by rw [Real.sq_sqrt (M.positive i).le]
    _ = _ := by ring

/-- An earlier polynomial is orthogonal to the next leading continuant of the actual reconstructed matrix.
Use: the quotient term in the Gaussian division proof has exactly zero original integral.
Article: main_krylov, Section 3, Gaussian quadrature exactness.
Proof: the reused normalized-continuant identity identifies the genuine
orthogonal polynomial; its positive coupling product is only a scalar factor. -/
theorem polynomialIntegral_leading_mul {N : ℕ} (M : DiscreteMeasure N)
    {m : ℕ} (hm : m<N) {q : ℝ[X]} (hq : q.natDegree<m) :
    polynomialIntegral M (M.reconstructed.data.leading m*q)=0 := by
  -- The input measure and its constructed Jacobi chain use the same actual orthogonal polynomials.
  have he := normalizedLeading_eq_orthogonalPolynomial M ⟨m, hm⟩
  have hl := linkProduct_pos M.reconstructed_irreducible hm
  have hpoly : M.reconstructed.data.leading m=M.reconstructed.data.linkProduct m • M.orthogonalPolynomial ⟨m, hm⟩ := by
    rw [← he, normalizedLeading, smul_eq_C_mul, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hl.ne', C_1, one_mul]
  have ho := M.polynomialBasis_orthogonal_lower (i := ⟨m, hm⟩) hq
  rw [← M.evaluate_orthogonalPolynomial, M.inner_evaluate] at ho
  rw [hpoly]
  change (∑ i, M.weight i*(M.reconstructed.data.linkProduct m • M.orthogonalPolynomial ⟨m, hm⟩*q).eval (M.node i))=0
  simp only [eval_mul, eval_smul, smul_eq_mul]
  calc
    _ = M.reconstructed.data.linkProduct m*∑ i, M.weight i*
        (M.orthogonalPolynomial ⟨m, hm⟩).eval (M.node i)*q.eval (M.node i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [ho, mul_zero]

/-- The actual leading Jacobi quadrature is exact for every polynomial of degree strictly below 2m.
Use: proves the Gaussian interpretation invoked by the CG error profile and later moment fibres.
Article: main_krylov, Section 3, m-point Gaussian quadrature.
Proof: divide by the actual monic degree-m continuant. The remainder has
degree below m and matches the leading block; the quotient has degree below m,
so its original integral vanishes by orthogonality and its quadrature vanishes by Cayley--Hamilton. -/
theorem gauss_exact {N : ℕ} (M : DiscreteMeasure N) {m : ℕ}
    (hm : 0<m) (hmN : m<N) {p : ℝ[X]} (hp : p.natDegree<2*m) :
    jacobiFunctional M.reconstructed.data m hm p=polynomialIntegral M p := by
  -- Both discarded terms are proved zero for independent mathematical reasons.
  let J := M.reconstructed
  let P := J.data.leading m
  let r := p %ₘ P
  let q := p /ₘ P
  have hP : P.Monic := J.data.block_monic J.coupling_nonneg 0 m
  have hdP : P.natDegree=m := J.data.block_natDegree J.coupling_nonneg 0 m
  have hq : q.natDegree<m := by
    dsimp only [q]
    rw [natDegree_divByMonic p hP, hdP]
    omega
  have hr : r.degree<m := by
    have h := degree_modByMonic_lt p hP
    rwa [degree_eq_natDegree hP.ne_zero, hdP] at h
  have hsplit : r+P*q=p := modByMonic_add_div p P
  have hz : jacobiFunctional J.data m hm (P*q)=0 := by
    have hchar : P=(J.data.matrix 0 m).charpoly := J.data.block_eq_charpoly J.coupling_nonneg 0 m
    change (aeval (J.data.matrix 0 m) (P*q)) ⟨0, hm⟩ ⟨0, hm⟩=0
    rw [map_mul, hchar, Matrix.aeval_self_charpoly, Matrix.zero_mul]
    rfl
  rw [← hsplit, map_add, map_add, hz, polynomialIntegral_leading_mul M hmN hq, add_zero, add_zero]
  rw [polynomialIntegral_reconstructed]
  exact jacobiFunctional_low_degree J.data J.coupling_nonneg hm hmN.le hr

/-- Gaussian polynomial exactness includes the full-support terminal block.
Use: the quadrature dictionary remains valid at active-spectrum exhaustion.
Article: main_krylov, Section 3, the full N-point rule.
Proof: a proper prefix uses the proved Gaussian division theorem; the full
block has the original measure's exact polynomial integral for every polynomial. -/
theorem gauss_exact_le {N : ℕ} (M : DiscreteMeasure N) {m : ℕ}
    (hm : 0<m) (hmN : m≤N) {p : ℝ[X]} (hp : p.natDegree<2*m) :
    jacobiFunctional M.reconstructed.data m hm p=polynomialIntegral M p := by
  by_cases hlt : m<N
  · exact gauss_exact M hm hlt hp
  · have he : m=N := by omega
    subst m
    exact (polynomialIntegral_reconstructed M p).symm

end
end krylov.Reference

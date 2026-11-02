import krylov.Reference.Gauss
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), Gaussian rules for the original Jacobi functional.
Use: extend the existing finite-measure quadrature proof to the original normalized polynomial integral with its stated Jacobi orthogonality.
Source: reuse the continuant polynomial sequence, low-degree spanning theorem, monic division and Cayley-Hamilton from the proved Gaussian quadrature construction.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2

/-- A normalized polynomial functional with the original Jacobi orthogonality agrees with the leading first-site rule on all degrees below its size.
Use: A normalized polynomial functional with the original Jacobi orthogonality agrees with the leading first-site rule on all degrees below its size.
Article: main_krylov, prop:phi(c), Gaussian rules for the original Jacobi functional.
Proof: Compare the two linear functionals on the existing degree-graded continuant basis. -/
theorem jacobiFunctional_orthogonal_low (J : JacobiData) (hJ : ∀ i,0≤J.aSq i)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (h1 : L 1=1)
    (ho : ∀ m q,q.natDegree<m → L (J.leading m*q)=0) {m : ℕ} (hm : 0 < m)
    {p : ℝ[X]} (hp : p.degree<m) : jacobiFunctional J m hm p=L p := by
  -- Compare the original integral and finite first-site rule on their common continuant polynomial basis.
  let S := leadingSequence J hJ
  have hspan := S.span_degreeLT (m := m) (fun i _ => isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i)))
  have hker : Submodule.span ℝ (S '' Set.Iio m)≤(jacobiFunctional J m hm-L).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change jacobiFunctional J m hm (J.leading i)-L (J.leading i)=0
    rw [jacobiFunctional_leading J hJ m hm hi]
    by_cases hz : i=0
    · subst i
      simp [h1]
    · have h := ho i 1 (by simp only [natDegree_one];omega)
      have hl : L (J.leading i)=0 := by simpa only [mul_one] using h
      rw [ite_eq_right hz,mul_zero,hl,sub_self]
  apply sub_eq_zero.mp
  apply hker
  rw [hspan,mem_degreeLT]
  exact hp

/-- The original Jacobi first-site spectral rule is exact through degree twice its size minus one for every normalized functional having those Jacobi recurrence polynomials.
Use: The original Jacobi first-site spectral rule is exact through degree twice its size minus one for every normalized functional having those Jacobi recurrence polynomials.
Article: main_krylov, prop:phi(c), Gaussian rules for the original Jacobi functional.
Proof: Divide by the actual leading continuant; orthogonality and Cayley-Hamilton remove the quotient, while the existing low-degree basis identifies the remainder. -/
theorem jacobiFunctional_gauss_exact (J : JacobiData) (hJ : ∀ i,0≤J.aSq i)
    (L : ℝ[X] →ₗ[ℝ] ℝ) (h1 : L 1=1)
    (ho : ∀ m q,q.natDegree<m → L (J.leading m*q)=0) {m : ℕ} (hm : 0 < m)
    {p : ℝ[X]} (hp : p.natDegree<2*m) : jacobiFunctional J m hm p=L p := by
  -- Use the original monic continuant in polynomial division before applying either orthogonality or the actual matrix characteristic identity.
  let P := J.leading m
  let r := p %ₘ P
  let q := p /ₘ P
  have hP : P.Monic := J.block_monic hJ 0 m
  have hdP : P.natDegree=m := J.block_natDegree hJ 0 m
  have hq : q.natDegree<m := by
    dsimp only [q]
    rw [natDegree_divByMonic p hP,hdP]
    omega
  have hr : r.degree<m := by
    have h := degree_modByMonic_lt p hP
    rwa [degree_eq_natDegree hP.ne_zero,hdP] at h
  have hsplit : r+P*q=p := modByMonic_add_div p P
  have hz : jacobiFunctional J m hm (P*q)=0 := by
    have hchar : P=(J.matrix 0 m).charpoly := J.block_eq_charpoly hJ 0 m
    change (aeval (J.matrix 0 m) (P*q)) ⟨0,hm⟩ ⟨0,hm⟩=0
    rw [map_mul,hchar,Matrix.aeval_self_charpoly,Matrix.zero_mul]
    rfl
  rw [← hsplit,map_add,map_add,hz,ho m q hq,add_zero,add_zero]
  exact jacobiFunctional_orthogonal_low J hJ L h1 ho hm hr
end
end krylov.Reference

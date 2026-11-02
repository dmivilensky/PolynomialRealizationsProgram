import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import jacobi.Finite.NormalizedPolynomials
import jacobi.Finite.FlowWeightLimits

/-!
The monic variational characterization used in finite flow sorting.
Every actual leading continuant minimizes the genuine weighted square
norm among monic polynomials of the same degree. This follows from the
constructed orthonormal polynomial basis, rather than an assumed limiting
polynomial family. Use: FlowSorting bounds its values at dominant atoms
by comparing with the polynomial vanishing at the earlier dominant atoms.
Article: jacobi, Proposition 5.5 and Section 5.6.
Article role: both sorted matrix limits, limiting Richardson energy and its quartic Jacobi
asymptotic.
-/
namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Real Polynomial chebyshev1 chebyshev2
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual squared polynomial norm in a positive finite measure.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
def polynomialSquareNorm {N : ℕ} (M : DiscreteMeasure N) (p : ℝ[X]) : ℝ :=
  ∑ j,M.weight j*(p.eval (M.node j))^2

/-- Actual monic continuants are orthogonal to every lower degree
polynomial in the original finite spectral measure.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem leading_orthogonal_lower {N : ℕ} (M : DiscreteMeasure N) (i : Fin N)
    {q : ℝ[X]} (hq : q.natDegree < i.val) :
    (∑ j,M.weight j*(M.reconstructed.data.leading i).eval (M.node j)*q.eval (M.node j))=0 := by
  have hl := linkProduct_pos M.reconstructed_irreducible i.isLt
  have h := M.polynomialBasis_orthogonal_lower hq
  rw [← M.evaluate_orthogonalPolynomial,← normalizedLeading_eq_orthogonalPolynomial,
    M.inner_evaluate] at h
  simp only [normalizedLeading,eval_mul,eval_C] at h
  have he : (∑ j,M.weight j*((M.reconstructed.data.linkProduct i)⁻¹*
      (M.reconstructed.data.leading i).eval (M.node j))*q.eval (M.node j))=
      (M.reconstructed.data.linkProduct i)⁻¹*
        ∑ j,M.weight j*(M.reconstructed.data.leading i).eval (M.node j)*q.eval (M.node j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hl.ne')

/-- The true monic orthogonal polynomial minimizes its square norm.
This elementary Pythagorean inequality is the quantitative sorting input.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem leading_minimum {N : ℕ} (M : DiscreteMeasure N) (i : Fin N)
    {q : ℝ[X]} (hqm : q.Monic) (hqd : q.natDegree=i.val) :
    M.polynomialSquareNorm (M.reconstructed.data.leading i)≤M.polynomialSquareNorm q := by
  let p := M.reconstructed.data.leading i
  have hpm : p.Monic := M.reconstructed.data.block_monic M.reconstructed.coupling_nonneg 0 i
  have hpd : p.natDegree=i.val :=
    M.reconstructed.data.block_natDegree M.reconstructed.coupling_nonneg 0 i
  by_cases hi : i.val=0
  · have hp : p=1 := eq_one_of_monic_natDegree_zero hpm (hpd.trans hi)
    have hq : q=1 := eq_one_of_monic_natDegree_zero hqm (hqd.trans hi)
    change M.polynomialSquareNorm p≤M.polynomialSquareNorm q
    rw [hp,hq]
  · have hdeg : (q-p).natDegree < i.val :=
      (show q.IsMonicOfDegree i.val from ⟨hqd,hqm⟩).natDegree_sub_lt hi ⟨hpd,hpm⟩
    have ho := M.leading_orthogonal_lower i hdeg
    have hn : 0≤M.polynomialSquareNorm (q-p) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (M.positive j).le (sq_nonneg _))
    have he : M.polynomialSquareNorm q=M.polynomialSquareNorm p+
        2*(∑ j,M.weight j*p.eval (M.node j)*(q-p).eval (M.node j))+
          M.polynomialSquareNorm (q-p) := by
      unfold polynomialSquareNorm
      rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [eval_sub]
      ring
    change (∑ j,M.weight j*p.eval (M.node j)*(q-p).eval (M.node j))=0 at ho
    rw [ho] at he
    linarith

end
end jacobi.Finite.DiscreteMeasure

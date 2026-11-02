import jacobi.Analysis.QuadraticError
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Pairing adjacent coordinates separates the nonalternating alpha kernel
from the alternating beta kernel. These exact finite identities retain
the Euclidean identity contribution with its necessary factor one half.
Use: paired_kernel_quadratic separates the first-edge Gram kernel.
-/
namespace jacobi.Analysis
noncomputable section

/-- The symmetric coordinate of an adjacent physical pair.
Use: paired_kernel_quadratic separates the first-edge Gram kernel.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def pairPlus {ι : Type*} (v : ι × Fin 2 → ℝ) (i : ι) : ℝ := v (i,0)+v (i,1)

/-- The antisymmetric coordinate of an adjacent physical pair.
Use: paired_kernel_quadratic separates the alternating second edge.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
-/
def pairMinus {ι : Type*} (v : ι × Fin 2 → ℝ) (i : ι) : ℝ := v (i,0)-v (i,1)

/-- The exact finite squared-norm identity for adjacent pairs.
Use: two continuum coercivity bounds control one original finite norm.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: expand the two actual coordinates in each pair; their cross
terms cancel, and sum the resulting scalar identity. -/
theorem paired_norm {ι : Type*} [Fintype ι] (v : ι × Fin 2 → ℝ) :
    (∑ i, (pairPlus v i)^2)+(∑ i, (pairMinus v i)^2) =
      2*∑ p, (v p)^2 := by
  rw [Fintype.sum_prod_type,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_two,pairPlus,pairMinus]
  ring

/-- The exact two-edge quadratic-form decomposition after pairing.
Use: the actual cell-integrated Gram form is the sum of its true alpha
form on P and beta form on Q, before any limiting approximation.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: regroup the finite product indices and evaluate the four terms
of each adjacent pair. Their parity signs give precisely the sum and
difference products; no alternating remainder is discarded. -/
theorem paired_kernel_quadratic {ι : Type*} [Fintype ι]
    (A B : ι→ι→ℝ) (v : ι × Fin 2 → ℝ) :
    (∑ p, ∑ q, (A p.1 q.1+(-1:ℝ)^(p.2.val+q.2.val)*B p.1 q.1)*v p*v q) =
      (∑ i, ∑ j, A i j*pairPlus v i*pairPlus v j)+
      (∑ i, ∑ j, B i j*pairMinus v i*pairMinus v j) := by
  -- Regroup the original four within-pair terms before simplifying their signs.
  simp only [Fintype.sum_prod_type]
  simp_rw [Fin.sum_univ_two]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  norm_num [pairPlus,pairMinus]
  ring

end
end jacobi.Analysis

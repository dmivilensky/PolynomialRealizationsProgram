import jacobi.Finite.Reconstruction
import Mathlib.Tactic.Linarith

/-!
Article: main_krylov, s2:eq:cg, lem:chris and apC:lem:stieltjes(a).
Use: construct the exterior Christoffel minimum and its unique minimizing
polynomial for every finite positive measure and every degree below its support size.
Source: the classical reproducing-kernel proof (GolubMeurant10); orthonormal
polynomials, their exact degrees and their actual L² basis are reused from jacobi.
-/

namespace krylov.Reference
noncomputable section
open Polynomial jacobi.Finite
open scoped InnerProductSpace BigOperators
variable {N : ℕ} (M : DiscreteMeasure N)

/-- A positive probability measure has nonempty support.
Use: the constant orthonormal polynomial supplies a positive Christoffel denominator.
Article: main_krylov, s2:eq:cg, normalized finite spectral measure.
Proof: an empty finite sum cannot have probability mass one. -/
theorem support_pos (M : DiscreteMeasure N) : 0<N := by
  by_contra h
  have hz : N=0 := by omega
  subst N
  have hp := M.probability
  simp at hp

/-- The degree-zero orthonormal polynomial of the actual probability measure is one.
Use: proves strict positivity of the Christoffel kernel at every real evaluation point.
Article: main_krylov, lem:chris, normalization of the orthogonal polynomials.
Proof: the existing first-basis theorem identifies its evaluation with the unit constant;
faithfulness below the support size identifies the actual polynomial. -/
theorem orthogonalPolynomial_first : M.orthogonalPolynomial ⟨0, support_pos M⟩=1 := by
  apply M.evaluate_injective
  · rw [(M.orthogonalPolynomial_degree _).1]
    exact support_pos M
  · simpa only [natDegree_one] using support_pos M
  · rw [M.evaluate_orthogonalPolynomial, M.polynomialBasis_first]

/-- Every polynomial combination through degree m has degree at most m.
Use: keeps all minimization competitors inside the actual admissible polynomial space.
Article: main_krylov, lem:chris, degree constraint.
Proof: above m each coefficient of each retained orthogonal polynomial is zero. -/
theorem polynomial_prefix_degree (m : ℕ) (c : Fin N → ℝ) :
    (∑ i : Fin N with i.val≤m, c i • M.orthogonalPolynomial i).natDegree≤m := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [coeff_smul, coeff_eq_zero_of_natDegree_lt
    (by rw [(M.orthogonalPolynomial_degree i).1]; exact lt_of_le_of_lt (Finset.mem_filter.mp hi).2 hk), smul_zero]

/-- The actual polynomial has its finite orthogonal expansion through its degree bound.
Use: supplies the reproducing identity at an arbitrary exterior point.
Article: main_krylov, lem:chris, finite polynomial reproducing kernel.
Proof: expand the genuine evaluation vector in the already constructed orthonormal
basis; higher coefficients vanish, and faithfulness recovers polynomial equality. -/
theorem polynomial_prefix_expansion {m : ℕ} (hm : m<N) {p : ℝ[X]} (hp : p.natDegree≤m) :
    p=∑ i : Fin N with i.val≤m,
      inner ℝ (M.polynomialBasis i) (M.evaluate p) • M.orthogonalPolynomial i := by
  -- Prove equality in the actual finite L² model before using polynomial faithfulness.
  apply M.evaluate_injective (hp.trans_lt hm) ((polynomial_prefix_degree M m _).trans_lt hm)
  change M.evaluation p=M.evaluation _
  rw [map_sum]
  simp only [map_smul, show ∀ i, M.evaluation (M.orthogonalPolynomial i)=M.polynomialBasis i from M.evaluate_orthogonalPolynomial]
  have he : (∑ i : Fin N with i.val≤m, inner ℝ (M.polynomialBasis i) (M.evaluate p) • M.polynomialBasis i)=
      ∑ i : Fin N, inner ℝ (M.polynomialBasis i) (M.evaluate p) • M.polynomialBasis i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hmi : m < i.val := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hi
    rw [M.polynomialBasis_orthogonal_lower (hp.trans_lt hmi), zero_smul]
  rw [he, M.polynomialBasis.sum_repr']
  rfl

/-- The actual finite reproducing-kernel polynomial at a real evaluation point.
Use: its normalization is the constructed Christoffel optimizer.
Article: main_krylov, apC:lem:stieltjes, K_m and the exterior minimizer. -/
def kernelPolynomial (m : ℕ) (a : ℝ) : ℝ[X] :=
  ∑ i : Fin N with i.val≤m, (M.orthogonalPolynomial i).eval a • M.orthogonalPolynomial i

/-- The positive Christoffel kernel diagonal, with the actual orthonormal normalization.
Use: the reciprocal is the minimum energy for value one at the evaluation point.
Article: main_krylov, lem:chris and apC:lem:stieltjes, K_m. -/
def christoffelKernel (m : ℕ) (a : ℝ) : ℝ :=
  ∑ i : Fin N with i.val≤m, ((M.orthogonalPolynomial i).eval a)^2

/-- The kernel polynomial evaluates to its sum-of-squares diagonal.
Use: proves the candidate minimizer has the prescribed value one.
Article: main_krylov, apC:lem:stieltjes(a).
Proof: evaluate the defining finite polynomial sum. -/
theorem kernelPolynomial_eval (m : ℕ) (a : ℝ) :
    (kernelPolynomial M m a).eval a=christoffelKernel M m a := by
  simp only [kernelPolynomial, christoffelKernel, eval_finsetSum, eval_smul, smul_eq_mul, pow_two]

/-- The actual kernel diagonal is strictly positive, including degree zero.
Use: justifies every division in the Christoffel optimizer and minimum.
Article: main_krylov, lem:chris, positive exterior minimum.
Proof: all summands are nonnegative squares and the constant polynomial contributes one. -/
theorem christoffelKernel_pos (m : ℕ) (a : ℝ) : 0<christoffelKernel M m a := by
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  refine ⟨⟨0, support_pos M⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.zero_le m⟩, ?_⟩
  rw [orthogonalPolynomial_first, eval_one, one_pow]
  exact zero_lt_one

/-- The actual kernel polynomial reproduces every admissible polynomial value.
Use: proves the minimization by orthogonal decomposition in the actual spectral L² norm.
Article: main_krylov, lem:chris and apC:lem:stieltjes(a).
Proof: evaluate the genuine orthogonal polynomial expansion at the chosen point. -/
theorem kernel_reproduces {m : ℕ} (hm : m<N) (a : ℝ) {p : ℝ[X]} (hp : p.natDegree≤m) :
    inner ℝ (M.evaluate (kernelPolynomial M m a)) (M.evaluate p)=p.eval a := by
  -- The actual expansion coefficients, rather than assumed orthogonal-polynomial data, reproduce evaluation.
  have hv := congrArg (fun q : ℝ[X] => q.eval a) (polynomial_prefix_expansion M hm hp)
  simp only [eval_finsetSum, eval_smul, smul_eq_mul] at hv
  change inner ℝ (M.evaluation _) (M.evaluate p)=_
  rw [kernelPolynomial, map_sum]
  simp only [map_smul, sum_inner, real_inner_smul_left, show ∀ i, M.evaluation (M.orthogonalPolynomial i)=M.polynomialBasis i from M.evaluate_orthogonalPolynomial]
  rw [hv]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- The constructed normalized kernel polynomial is the candidate Christoffel optimizer.
Use: gives the actual polynomial, rather than only an abstract minimum value.
Article: main_krylov, lem:chris, unique exterior minimizing polynomial. -/
def christoffelPolynomial (m : ℕ) (a : ℝ) : ℝ[X] :=
  (christoffelKernel M m a)⁻¹ • kernelPolynomial M m a

/-- The constructed Christoffel polynomial is admissible.
Use: the minimum is attained by an explicitly constructed polynomial.
Article: main_krylov, lem:chris and apC:lem:stieltjes(a).
Proof: scalar multiplication preserves the degree bound and cancels the strictly positive kernel diagonal. -/
theorem christoffelPolynomial_admissible (m : ℕ) (a : ℝ) :
    (christoffelPolynomial M m a).natDegree≤m ∧ (christoffelPolynomial M m a).eval a=1 := by
  refine ⟨(natDegree_smul_le _ _).trans (polynomial_prefix_degree M m _), ?_⟩
  simp only [christoffelPolynomial, eval_smul, smul_eq_mul, kernelPolynomial_eval,
    inv_mul_cancel₀ (christoffelKernel_pos M m a).ne']

/-- The actual normalized kernel has the reciprocal kernel energy.
Use: identifies the attained numerical Christoffel minimum.
Article: main_krylov, apC:lem:stieltjes(a), λ_m(a)=1/K_m(a).
Proof: reproduction gives the kernel squared norm; normalize by its actual positive diagonal. -/
theorem christoffelPolynomial_norm {m : ℕ} (hm : m<N) (a : ℝ) :
    ‖M.evaluate (christoffelPolynomial M m a)‖^2=(christoffelKernel M m a)⁻¹ := by
  -- Reproduction identifies the actual kernel energy before the positive normalization is canceled.
  have hk := kernel_reproduces M hm a (polynomial_prefix_degree M m
    (fun i => (M.orthogonalPolynomial i).eval a))
  change inner ℝ (M.evaluate (kernelPolynomial M m a)) (M.evaluate (kernelPolynomial M m a))=
    (kernelPolynomial M m a).eval a at hk
  rw [kernelPolynomial_eval, real_inner_self_eq_norm_sq] at hk
  change ‖M.evaluation ((christoffelKernel M m a)⁻¹ • kernelPolynomial M m a)‖^2=_
  rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change (christoffelKernel M m a)⁻¹^2*‖M.evaluate (kernelPolynomial M m a)‖^2=_
  rw [hk]
  field_simp

/-- Every admissible polynomial has the exact orthogonal excess over the Christoffel minimum.
Use: supplies minimization and uniqueness with a quantitative equality case.
Article: main_krylov, lem:chris, the exterior Christoffel minimum.
Proof: the difference has value zero at the evaluation point, hence reproduction
makes it orthogonal to the normalized kernel; Pythagoras gives the formula. -/
theorem christoffel_excess {m : ℕ} (hm : m<N) (a : ℝ) {p : ℝ[X]}
    (hp : p.natDegree≤m) (ha : p.eval a=1) :
    ‖M.evaluate p‖^2=(christoffelKernel M m a)⁻¹+
      ‖M.evaluate (p-christoffelPolynomial M m a)‖^2 := by
  -- Reproduction kills the zero-value difference exactly, before taking any norm bounds.
  have hd := (natDegree_sub_le p (christoffelPolynomial M m a)).trans
    (max_le hp (christoffelPolynomial_admissible M m a).1)
  have ho : inner ℝ (M.evaluate (christoffelPolynomial M m a))
      (M.evaluate (p-christoffelPolynomial M m a))=0 := by
    change inner ℝ (M.evaluation ((christoffelKernel M m a)⁻¹ • _)) _=0
    rw [map_smul, real_inner_smul_left]
    change (christoffelKernel M m a)⁻¹*inner ℝ (M.evaluate (kernelPolynomial M m a)) _=0
    rw [kernel_reproduces M hm a hd,
      eval_sub, ha, (christoffelPolynomial_admissible M m a).2, sub_self, mul_zero]
  have he : M.evaluate p=M.evaluate (christoffelPolynomial M m a)+
      M.evaluate (p-christoffelPolynomial M m a) := by
    change M.evaluation p=M.evaluation _+M.evaluation _
    rw [map_sub]
    abel
  calc
    _ = ‖M.evaluate (christoffelPolynomial M m a)+M.evaluate (p-christoffelPolynomial M m a)‖^2 := congrArg (fun v => ‖v‖^2) he
    _ = _ := by rw [norm_add_sq_real, ho, christoffelPolynomial_norm M hm a]; ring

/-- The constructed polynomial uniquely attains the minimum among all admissible degree-m polynomials.
Use: the exterior Christoffel statement includes its optimizer and its equality case.
Article: main_krylov, lem:chris and apC:lem:stieltjes(a).
Proof: the excess is a squared norm; equality forces zero weighted evaluation
and faithfulness below the number of atoms forces equality of polynomials. -/
theorem christoffel_minimum_unique {m : ℕ} (hm : m<N) (a : ℝ) {p : ℝ[X]}
    (hp : p.natDegree≤m) (ha : p.eval a=1) :
    (christoffelKernel M m a)⁻¹≤‖M.evaluate p‖^2 ∧
      (‖M.evaluate p‖^2=(christoffelKernel M m a)⁻¹ ↔ p=christoffelPolynomial M m a) := by
  -- A zero excess is a zero actual evaluation vector, so the polynomial root bound supplies uniqueness.
  have he := christoffel_excess M hm a hp ha
  refine ⟨by nlinarith [sq_nonneg ‖M.evaluate (p-christoffelPolynomial M m a)‖], ?_⟩
  constructor
  · intro h
    have hz : M.evaluate (p-christoffelPolynomial M m a)=0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (M.evaluate (p-christoffelPolynomial M m a))]
    exact sub_eq_zero.mp (M.evaluate_eq_zero
      ((natDegree_sub_le _ _).trans_lt (max_lt (hp.trans_lt hm)
        ((christoffelPolynomial_admissible M m a).1.trans_lt hm))) hz)
  · rintro rfl
    exact christoffelPolynomial_norm M hm a

end
end krylov.Reference

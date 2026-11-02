import krylov.LinearAlgebra.SchurProduct
import chebyshev1.Spectral.Weights
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Use: derive actual real zeros, simplicity, normalization, positivity and monotonicity of the true Schur continuation from its original positive eigenvalues.
Source: actual finite spectral determinant product, real positive reciprocal factors and the elementary finite product rule.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Polynomial
open scoped BigOperators
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual normalized continuation product formed from the true positive matrix spectrum.
Use: The actual normalized continuation product formed from the true positive matrix spectrum.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Use the genuine original spectral labels, retaining empty products. -/
def spectralContinuation (S : Matrix n n ℝ) (hS : S.PosDef) : ℝ[X] :=
  ∏ i, (1-C ((hS.1.eigenvalues i)⁻¹)*X)

/-- The actual spectral continuation evaluates to the genuine inverse-normalized matrix determinant.
Use: The actual spectral continuation evaluates to the genuine inverse-normalized matrix determinant.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Evaluate the true polynomial product and use the proved actual spectral determinant formula. -/
theorem spectralContinuation_eval (S : Matrix n n ℝ) (hS : S.PosDef) (lam : ℝ) :
    (spectralContinuation S hS).eval lam=(1-lam • S⁻¹).det := by
  rw [positive_normalized_shift_product S hS lam]
  simp only [spectralContinuation,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- The actual normalized spectral continuation takes value one at zero.
Use: The actual normalized spectral continuation takes value one at zero.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Every genuine finite spectral factor equals one. -/
theorem spectralContinuation_zero (S : Matrix n n ℝ) (hS : S.PosDef) :
    (spectralContinuation S hS).eval 0=1 := by
  simp [spectralContinuation,eval_prod]

/-- The actual real continuation zeros are exactly the genuine original matrix eigenvalues.
Use: The actual real continuation zeros are exactly the genuine original matrix eigenvalues.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: A finite product vanishes precisely when an actual positive reciprocal factor vanishes. -/
theorem spectralContinuation_roots (S : Matrix n n ℝ) (hS : S.PosDef) (lam : ℝ) :
    (spectralContinuation S hS).eval lam=0 ↔ ∃ i,hS.1.eigenvalues i=lam := by
  -- Each genuine positive eigenvalue is nonzero, so the actual reciprocal factor has exactly that real zero.
  simp only [spectralContinuation,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X,
    Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
  apply exists_congr
  intro i
  have hp := hS.eigenvalues_pos i
  constructor <;> intro h
  · field_simp [hp.ne'] at h
    linarith
  · rw [← h]
    simp only [inv_mul_cancel₀ hp.ne',sub_self]

/-- Every genuine continuation zero is simple when the actual spectrum is injective.
Use: Every genuine continuation zero is simple when the actual spectrum is injective.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Isolate the true vanishing factor; the actual remaining factors are nonzero by genuine eigenvalue distinctness. -/
theorem spectralContinuation_simple (S : Matrix n n ℝ) (hS : S.PosDef)
    (hinj : Function.Injective hS.1.eigenvalues) (i : n) :
    (spectralContinuation S hS).derivative.eval (hS.1.eigenvalues i)≠0 := by
  -- Isolate the unique genuine zero before differentiating the actual product.
  rw [spectralContinuation,← Finset.mul_prod_erase Finset.univ
    (fun j => (1-C ((hS.1.eigenvalues j)⁻¹)*X : ℝ[X])) (Finset.mem_univ i),derivative_mul]
  simp only [derivative_sub,derivative_one,derivative_mul,derivative_C,zero_mul,
    derivative_X,mul_one,zero_add,zero_sub,eval_add,eval_mul,eval_neg,eval_C,
    eval_sub,eval_one,eval_X,inv_mul_cancel₀ (hS.eigenvalues_pos i).ne',sub_self,
    zero_mul,add_zero,eval_prod]
  apply mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (hS.eigenvalues_pos i).ne'))
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj hzero
  have hne := (Finset.mem_erase.mp hj).1
  have hp := hS.eigenvalues_pos j
  have he : hS.1.eigenvalues j=hS.1.eigenvalues i := by
    field_simp [hp.ne'] at hzero
    linarith
  exact hne (hinj he)

/-- The true continuation is positive strictly below all its actual eigenvalues.
Use: The true continuation is positive strictly below all its actual eigenvalues.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Every actual reciprocal spectral factor is positive. -/
theorem spectralContinuation_pos (S : Matrix n n ℝ) (hS : S.PosDef) (lam : ℝ)
    (hlam : ∀ i,lam<hS.1.eigenvalues i) :
    0 < (spectralContinuation S hS).eval lam := by
  -- Every actual factor is positive on the common open half-line below the true spectrum.
  simp only [spectralContinuation,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  apply Finset.prod_pos
  intro i _
  have h : (hS.1.eigenvalues i)⁻¹*lam<1 := by
    rw [mul_comm,← div_eq_mul_inv,div_lt_one (hS.eigenvalues_pos i)]
    exact hlam i
  linarith

/-- The actual continuation is nonincreasing below its genuine smallest eigenvalue.
Use: The actual continuation is nonincreasing below its genuine smallest eigenvalue.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: Each true positive spectral factor decreases and finite products preserve this order. -/
theorem spectralContinuation_antitone (S : Matrix n n ℝ) (hS : S.PosDef) (x y : ℝ)
    (hxy : x≤y) (hy : ∀ i,y<hS.1.eigenvalues i) :
    (spectralContinuation S hS).eval y≤(spectralContinuation S hS).eval x := by
  -- Compare each genuine positive reciprocal factor before taking the actual finite product.
  simp only [spectralContinuation,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  apply Finset.prod_le_prod₀
  · intro i _
    have h : (hS.1.eigenvalues i)⁻¹*y<1 := by
      rw [mul_comm,← div_eq_mul_inv,div_lt_one (hS.eigenvalues_pos i)]
      exact hy i
    linarith
  · intro i _
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr (hS.eigenvalues_pos i).le)) 1

/-- The actual continuation is strictly decreasing below its true spectrum whenever its genuine dimension is positive.
Use: The actual continuation is strictly decreasing below its true spectrum whenever its genuine dimension is positive.
Article: main_krylov, prop:phi(a), genuine positive spectral continuation factors.
Proof: All real factors are positive and at least one genuine reciprocal factor decreases strictly. -/
theorem spectralContinuation_strictAnti [Nonempty n] (S : Matrix n n ℝ) (hS : S.PosDef) (x y : ℝ)
    (hxy : x<y) (hy : ∀ i,y<hS.1.eigenvalues i) :
    (spectralContinuation S hS).eval y<(spectralContinuation S hS).eval x := by
  -- The genuine dimension supplies a strictly decreasing factor while every actual factor remains positive.
  -- The real lower factor product is strictly positive, including all negative evaluation points.
  simp only [spectralContinuation,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X]
  apply Finset.prod_lt_prod₀
  · intro i _
    have h : (hS.1.eigenvalues i)⁻¹*y<1 := by
      rw [mul_comm,← div_eq_mul_inv,div_lt_one (hS.eigenvalues_pos i)]
      exact hy i
    linarith
  · intro i _
    exact (sub_lt_sub_left (mul_lt_mul_of_pos_left hxy (inv_pos.mpr (hS.eigenvalues_pos i))) 1).le
  · obtain ⟨i⟩ := ‹Nonempty n›
    exact ⟨i,Finset.mem_univ i,sub_lt_sub_left (mul_lt_mul_of_pos_left hxy (inv_pos.mpr (hS.eigenvalues_pos i))) 1⟩
end
end krylov.LinearAlgebra

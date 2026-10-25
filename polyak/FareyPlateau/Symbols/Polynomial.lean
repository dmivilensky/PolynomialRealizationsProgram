import polyak.FareyPlateau.Symbols.Positivity
import Mathlib.Algebra.Polynomial.Derivative

/-! Cancellation at c=1 is performed exactly in the polynomial ring.  The
resulting rational function is the source phase floor, with its prescribed
endpoint values. -/
noncomputable section
namespace polyak.FareyPlateau.Symbols
open Polynomial Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

def lagDenominatorPolynomial (n : ℤ) : ℝ[X] :=
  (Chebyshev.T ℝ n-1) /ₘ (X-C 1)

theorem lagDenominator_factor (n : ℤ) :
    (X-C 1)*lagDenominatorPolynomial n=Chebyshev.T ℝ n-1 := by
  apply Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
  simp [Polynomial.IsRoot,Chebyshev.T_eval_one]

theorem lagDenominator_eval (n : ℤ) (c : ℝ) :
    (1-c)*(lagDenominatorPolynomial n).eval c=1-(Chebyshev.T ℝ n).eval c := by
  have he := congrArg (fun p : ℝ[X]=>p.eval c) (lagDenominator_factor n)
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_one] at he
  linarith

@[simp] theorem lagDenominator_one (n : ℤ) :
    (lagDenominatorPolynomial n).eval 1=(n:ℝ)^2 := by
  have he := congrArg (fun p : ℝ[X]=>(derivative p).eval 1) (lagDenominator_factor n)
  simp only [derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,
    derivative_one,eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,
    one_mul,zero_mul,add_zero,Chebyshev.derivative_T_eval_one] at he
  exact he

def normalizedDenominator (n : I→ℤ) (w : I→ℝ) : ℝ[X] :=
  ∑i,C (w i)*lagDenominatorPolynomial (n i)

def sinePolynomial (n : I→ℤ) (w : I→ℝ) : ℝ[X] :=
  ∑i,C (w i)*Chebyshev.U ℝ (n i-1)

theorem normalizedDenominator_cos (n : I→ℤ) (w : I→ℝ) (ω : ℝ) :
    (1-Real.cos ω)*(normalizedDenominator n w).eval (Real.cos ω)=denominator n w ω := by
  simp only [normalizedDenominator,denominator,eval_finsetSum,eval_mul,eval_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := lagDenominator_eval (n i) (Real.cos ω)
  rw [Chebyshev.T_real_cos] at he
  linear_combination w i*he

@[simp] theorem normalizedDenominator_one (n : I→ℤ) (w : I→ℝ) :
    (normalizedDenominator n w).eval 1=∑i,w i*(n i:ℝ)^2 := by
  simp only [normalizedDenominator,eval_finsetSum,eval_mul,eval_C,lagDenominator_one]

theorem sinePolynomial_cos (n : I→ℤ) (w : I→ℝ) (ω : ℝ) :
    (sinePolynomial n w).eval (Real.cos ω)*Real.sin ω=
      ∑i,w i*Real.sin ((n i:ℝ)*ω) := by
  simp only [sinePolynomial,eval_finsetSum,eval_mul,eval_C,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have he := Chebyshev.U_real_cos ω (n i-1)
  simp only [Int.cast_sub,Int.cast_one,sub_add_cancel] at he
  linear_combination w i*he

@[simp] theorem sinePolynomial_one (n : I→ℤ) (w : I→ℝ) :
    (sinePolynomial n w).eval 1=∑i,w i*(n i:ℝ) := by
  simp only [sinePolynomial,eval_finsetSum,eval_mul,eval_C,Chebyshev.U_eval_one,
    Int.cast_sub,Int.cast_one,sub_add_cancel]

def psi (n : I→ℤ) (w : I→ℝ) (c : ℝ) : ℝ :=
  (1+c)*(sinePolynomial n w).eval c/(normalizedDenominator n w).eval c

@[simp] theorem psi_one (n : I→ℤ) (w : I→ℝ) :
    psi n w 1=2*(∑i,w i*(n i:ℝ))/(∑i,w i*(n i:ℝ)^2) := by
  norm_num [psi]

@[simp] theorem psi_neg_one (n : I→ℤ) (w : I→ℝ) : psi n w (-1)=0 := by
  simp [psi]

end polyak.FareyPlateau.Symbols

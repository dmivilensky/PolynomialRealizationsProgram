import nesterov.Faithful.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Exact finite-polynomial representation of every real circle symbol. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial
open scoped BigOperators

def circleProductPolynomial (N : ℕ) (A B : Polynomial ℝ) (r : ℝ) : Polynomial ℝ :=
  ∑ i∈Finset.range N,∑ j∈Finset.range N,
    C (A.coeff i*B.coeff j*r^(i+j))*(Polynomial.Chebyshev.T ℝ ((i:ℤ)-j)).comp (1-X)

theorem phase_cross_re (ω : ℝ) (i j : ℕ) :
    (circle ω^i*star (circle ω^j)).re=Real.cos (((i:ℝ)-j)*ω) := by
  have hre (n : ℕ) : (circle ω^n).re=Real.cos (n*ω) := by
    simpa [circle,polyak.Waves.z] using polyak.Waves.z_pow_re 0 ω n
  have him (n : ℕ) : (circle ω^n).im=Real.sin (n*ω) := by
    simpa [circle,polyak.Waves.z] using polyak.Waves.z_pow_im 0 ω n
  simp only [Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im,hre,him,
    sub_mul,Real.cos_sub]
  ring

theorem evalComplex_mul_phase (p : Polynomial ℝ) (r ω : ℝ) {N : ℕ}
    (hN : p.natDegree<N) :
    evalComplex p ((r:ℂ)*circle ω)=∑ i∈Finset.range N,(p.coeff i*r^i:ℝ)*circle ω^i := by
  have hNm : (p.map Complex.ofRealHom).natDegree<N := natDegree_map_le.trans_lt hN
  rw [evalComplex,eval_eq_sum_range' hNm]
  simp only [Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro i _
  change ((p.coeff i:ℝ):ℂ)*((r:ℂ)*circle ω)^i=((p.coeff i*r^i:ℝ):ℂ)*circle ω^i
  push_cast
  rw [mul_pow]
  ring

theorem circleProductPolynomial_eval (A B : Polynomial ℝ) (r ω : ℝ) {N : ℕ}
    (hA : A.natDegree<N) (hB : B.natDegree<N) :
    (circleProductPolynomial N A B r).eval (1-Real.cos ω)=
      (evalComplex A ((r:ℂ)*circle ω)*star (evalComplex B ((r:ℂ)*circle ω))).re := by
  rw [evalComplex_mul_phase A r ω hA,evalComplex_mul_phase B r ω hB]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum,map_mul,Complex.star_def,Complex.conj_ofReal,
    Complex.re_sum,circleProductPolynomial,eval_finsetSum,eval_mul,eval_C,eval_comp,
    eval_sub,eval_one,eval_X,sub_sub_cancel,Polynomial.Chebyshev.T_real_cos]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : ((A.coeff i*r^i:ℝ):ℂ)*circle ω^i*
      (((B.coeff j*r^j:ℝ):ℂ)*star (circle ω^j))=
      (A.coeff i*B.coeff j*r^(i+j):ℝ)*(circle ω^i*star (circle ω^j)) := by
    push_cast
    rw [pow_add]
    ring
  simp only [Complex.star_def] at he
  rw [he]
  have hp := phase_cross_re ω i j
  simp only [Complex.star_def] at hp
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hp]
  push_cast
  ring

end
end nesterov.Faithful

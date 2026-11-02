import chebyshev1.Stepsize.LowerBound
import bezout.Lower.EndpointGain

/-!
Article: bezout, Proposition D.1, exact root-step endpoint energies and correlation.
Use: the diagonal physical root-step profiles are calculated from their actual
prefix/suffix kernels; no energy or endpoint profile is assumed.
Proof: finite product differentiation gives the diagonal and cross identities,
then the exact Chebyshev terminal and its endpoint derivatives give the formulas.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The actual physical insertion kernel on a single spectral mode. -/
def diagonalKernel (γ : ℕ → ℝ) (N s : ℕ) (x : ℝ) : ℝ :=
  (chebyshev1.Stepsize.realization γ).kernel N s x x

/-- The full correlation of two actual diagonal channel profiles. -/
def crossEnergy (γ : ℕ → ℝ) (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ s ∈ Finset.range N, diagonalKernel γ N s x * diagonalKernel γ N s y

/-- Adding the last actual gradient step updates both profile factors causally. -/
theorem crossEnergy_succ (γ : ℕ → ℝ) (N : ℕ) (x y : ℝ) :
    crossEnergy γ (N+1) x y = (1-γ N*x)*(1-γ N*y)*crossEnergy γ N x y +
      (γ N)^2 * (chebyshev1.Stepsize.polynomial γ N).eval x *
        (chebyshev1.Stepsize.polynomial γ N).eval y := by
  unfold crossEnergy diagonalKernel
  rw [Finset.sum_range_succ, chebyshev1.Stepsize.kernel_last, chebyshev1.Stepsize.kernel_last]
  have hsum : (∑ s ∈ Finset.range N,
      (chebyshev1.Stepsize.realization γ).kernel (N+1) s x x *
        (chebyshev1.Stepsize.realization γ).kernel (N+1) s y y) =
      (1-γ N*x)*(1-γ N*y) * ∑ s ∈ Finset.range N,
        (chebyshev1.Stepsize.realization γ).kernel N s x x *
          (chebyshev1.Stepsize.realization γ).kernel N s y y := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [chebyshev1.Stepsize.kernel_extend γ N s (Finset.mem_range.mp hs),
      chebyshev1.Stepsize.kernel_extend γ N s (Finset.mem_range.mp hs)]
    ring
  rw [hsum]
  ring

/-- Exact cross-logarithmic-derivative identity, free of root denominators. -/
theorem crossEnergy_derivatives (γ : ℕ → ℝ) (N : ℕ) (x y : ℝ) :
    (y-x)*crossEnergy γ N x y =
      (chebyshev1.Stepsize.polynomial γ N).derivative.eval x *
        (chebyshev1.Stepsize.polynomial γ N).eval y -
      (chebyshev1.Stepsize.polynomial γ N).eval x *
        (chebyshev1.Stepsize.polynomial γ N).derivative.eval y := by
  induction N with
  | zero => simp [crossEnergy, chebyshev1.Stepsize.polynomial]
  | succ N ih =>
    rw [crossEnergy_succ]
    simp only [chebyshev1.Stepsize.polynomial, derivative_mul, derivative_sub,
      derivative_one, derivative_C, derivative_X, zero_mul, mul_one, zero_add,
      eval_add, eval_sub, eval_mul, eval_one, eval_C, eval_X, eval_zero]
    linear_combination (1-γ N*x)*(1-γ N*y)*ih

/-- The actual squared diagonal profile is p'^2-p p'', including every root. -/
theorem diagonalEnergy_derivatives (γ : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    crossEnergy γ N x x = (chebyshev1.Stepsize.polynomial γ N).derivative.eval x ^ 2 -
      (chebyshev1.Stepsize.polynomial γ N).eval x *
        (chebyshev1.Stepsize.polynomial γ N).derivative.derivative.eval x := by
  simpa only [crossEnergy, diagonalKernel, pow_two] using
    chebyshev1.Stepsize.kernel_square_sum_derivatives γ N x

/-- Reflection preserves an even first-kind Chebyshev polynomial. -/
theorem even_T_comp_neg (N : ℕ) (hN : Even N) : (T ℝ N).comp (-X)=T ℝ N := by
  have he : Even (N:ℤ) := by exact_mod_cast hN
  apply Polynomial.funext
  intro x
  norm_num [eval_comp, T_eval_neg, Int.negOnePow_even _ he]

/-- The even-degree Chebyshev first derivative at the left endpoint. -/
theorem even_T_derivative_neg_one (N : ℕ) (hN : Even N) :
    (T ℝ N).derivative.eval (-1)=-(N:ℝ)^2 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 1) (even_T_comp_neg N hN)
  norm_num [derivative_comp, derivative_T_eval_one] at h
  linarith

/-- The even-degree second derivative has equal values at both endpoints. -/
theorem even_T_second_derivative_neg_one (N : ℕ) (hN : Even N) :
    (T ℝ N).derivative.derivative.eval (-1)=(N:ℝ)^2*((N:ℝ)^2-1)/3 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.derivative.eval 1) (even_T_comp_neg N hN)
  simp [derivative_comp] at h
  have he := iterate_derivative_T_eval_one_eq_div (𝔽 := ℝ) N 2
  have he' : (T ℝ N).derivative.derivative.eval 1 = (N:ℝ)^2*((N:ℝ)^2-1)/3 := by
    simpa [Finset.prod_range_succ, Function.iterate_succ_apply'] using he
  exact h.trans he'

/-- The physical upper endpoint maps to minus one in the Chebyshev chart. -/
theorem z_upper (I : chebyshev1.SpectralInterval) : I.z I.L = -1 := by
  unfold chebyshev1.SpectralInterval.z chebyshev1.SpectralInterval.delta
  have hd := ne_of_gt I.delta_pos
  unfold chebyshev1.SpectralInterval.delta at hd
  field_simp
  ring

/-- All three physical terminal endpoint values needed by the even root-profile calculation. -/
theorem residual_L_even (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : Even N) :
    (I.residual N).eval I.L=I.epsilon N ∧
    (I.residual N).derivative.eval I.L=(2/I.delta)*I.epsilon N*(N:ℝ)^2 ∧
    (I.residual N).derivative.derivative.eval I.L=
      (2/I.delta)^2*I.epsilon N*((N:ℝ)^2*((N:ℝ)^2-1)/3) := by
  have he : Even (N:ℤ) := by exact_mod_cast hN
  have ha : I.eta-2/I.delta*I.L = -1 := by rw [← I.z_eq,z_upper I]
  constructor
  · rw [I.residual_eval,z_upper I,T_eval_neg_one,Int.negOnePow_even _ he]
    simp [chebyshev1.SpectralInterval.epsilon]
  · constructor
    · simp [chebyshev1.SpectralInterval.residual, derivative_comp, ha,
        even_T_derivative_neg_one N hN, chebyshev1.SpectralInterval.epsilon]
      ring
    · simp [chebyshev1.SpectralInterval.residual, derivative_comp, derivative_mul, ha,
        even_T_second_derivative_neg_one N hN, chebyshev1.SpectralInterval.epsilon]
      ring

/-- The actual root-step endpoint energy is the exact quartic polynomial stated in D.1. -/
theorem endpointEnergy_mu (γ : ℕ → ℝ) (I : chebyshev1.SpectralInterval) (N : ℕ)
    (he : chebyshev1.Stepsize.FinalExact γ I N) :
    crossEnergy γ N I.mu I.mu = (2*I.epsilon N/I.delta)^2*((2*(N:ℝ)^4+(N:ℝ)^2)/3) := by
  simpa only [crossEnergy, diagonalKernel, pow_two] using
    chebyshev1.Stepsize.endpoint_square_sum γ I N he

/-- At even horizons the second endpoint has exactly the same root-step energy. -/
theorem endpointEnergy_L (γ : ℕ → ℝ) (I : chebyshev1.SpectralInterval) (N : ℕ)
    (hN : Even N) (he : chebyshev1.Stepsize.FinalExact γ I N) :
    crossEnergy γ N I.L I.L = (2*I.epsilon N/I.delta)^2*((2*(N:ℝ)^4+(N:ℝ)^2)/3) := by
  rw [diagonalEnergy_derivatives, chebyshev1.Stepsize.final_polynomial_eq γ I N he,
    (residual_L_even I N hN).1, (residual_L_even I N hN).2.1, (residual_L_even I N hN).2.2]
  ring

/-- The exact signed correlation of the even-horizon endpoint profiles. -/
theorem endpointCross_even (γ : ℕ → ℝ) (I : chebyshev1.SpectralInterval) (N : ℕ)
    (hN : Even N) (he : chebyshev1.Stepsize.FinalExact γ I N) :
    crossEnergy γ N I.mu I.L=-(2*I.epsilon N/I.delta)^2*(N:ℝ)^2 := by
  have h := crossEnergy_derivatives γ N I.mu I.L
  rw [chebyshev1.Stepsize.final_polynomial_eq γ I N he,
    I.residual_derivative_eval_mu, I.residual_eval_mu,
    (residual_L_even I N hN).1, (residual_L_even I N hN).2.1] at h
  have hd := ne_of_gt I.delta_pos
  have heq : crossEnergy γ N I.mu I.L =
      ((-(2/I.delta)*I.epsilon N*(N:ℝ)^2)*I.epsilon N -
        I.epsilon N*((2/I.delta)*I.epsilon N*(N:ℝ)^2))/I.delta := by
    apply (eq_div_iff hd).mpr
    simpa only [chebyshev1.SpectralInterval.delta, mul_comm] using h
  rw [heq]
  field_simp
  ring

end
end bezout.Channel.Roots

import chebyshev1.Realization.Gain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
Article: jacobi, Theorem 5.1.
The genuine polynomial fundamental solutions of the rescaled Nesterov
recurrence have the sharp endpoint bound on the whole spectral interval.
Use: NesterovKernel identifies the actual first-variation kernels; their
spectral supremum is attained simultaneously at the zero spectral pair.
Source: Chebyshev polynomials of the second kind, reused from chebyshev1.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Polynomial.Chebyshev Set
set_option backward.isDefEq.respectTransparency false

/-- The polynomial fundamental solution of v_(s+1)=2*(1-lambda)*v_s-(1-lambda)*v_(s-1).
Use: its actual evaluated recurrence propagates one Hessian insertion in NesterovKernel.
Article: jacobi, Theorem 5.1.
-/
def nesterovWavePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 2*(1-X)
  | n+2 => 2*(1-X)*nesterovWavePolynomial (n+1)-(1-X)*nesterovWavePolynomial n

/-- The actual real spectral fundamental solution, evaluated from its genuine polynomial.
Use: nesterovWave_bound and nesterov_kernel prove the sharp full spectral gain.
Article: jacobi, Theorem 5.1.
-/
def nesterovWave (j:ℕ) (l:ℝ) : ℝ := (nesterovWavePolynomial j).eval l

/-- The fundamental solution starts at one.
Use: starts the actual Nesterov forward and insertion propagators.
Article: jacobi, Theorem 5.1.
Proof: evaluate the initial constant polynomial. -/
@[simp] theorem nesterovWave_zero (l:ℝ) : nesterovWave 0 l=1 := by simp [nesterovWave,nesterovWavePolynomial]

/-- The first fundamental step is exactly twice the Landweber factor.
Use: initializes the rescaled two-step Nesterov propagator.
Article: jacobi, Theorem 5.1.
Proof: evaluate the initial linear polynomial. -/
@[simp] theorem nesterovWave_one (l:ℝ) : nesterovWave 1 l=2*(1-l) := by simp [nesterovWave,nesterovWavePolynomial]

/-- The actual polynomial waves satisfy the rescaled Nesterov recurrence at every real spectral value.
Use: proves forward queries and tail propagation without dividing by a vanishing Landweber factor.
Article: jacobi, Theorem 5.1.
Proof: polynomial evaluation preserves the defining recurrence. -/
theorem nesterovWave_recurrence (j:ℕ) (l:ℝ) :
    nesterovWave (j+2) l=2*(1-l)*nesterovWave (j+1) l-(1-l)*nesterovWave j l := by
  simp [nesterovWave,nesterovWavePolynomial]

/-- The polynomial fundamental solution has the printed Chebyshev formula on the whole physical spectral interval.
Use: its sharp absolute bound follows from the already formalized second-kind Chebyshev bound.
Article: jacobi, Theorem 5.1.
Proof: the nonnegative square root squares to 1-lambda. The true Chebyshev recurrence and its two initial values therefore agree with the actual polynomial recurrence. -/
theorem nesterovWave_chebyshev (j:ℕ) {l:ℝ} (hl:l≤1) :
    nesterovWave j l=(Real.sqrt (1-l))^j*(U ℝ (j:ℤ)).eval (Real.sqrt (1-l)) := by
  -- The formula includes lambda=1; no division by its square root occurs.
  have hs : (Real.sqrt (1-l))^2=1-l := Real.sq_sqrt (sub_nonneg.mpr hl)
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simp; nlinarith [hs]
  | more n h0 h1 =>
    rw [nesterovWave_recurrence,h0,h1]
    rw [show ((n+2:ℕ):ℤ)=(n:ℤ)+2 by omega,U_add_two]
    simp only [eval_sub,eval_mul,eval_ofNat,eval_X]
    rw [show (n:ℤ)+1=((n+1:ℕ):ℤ) by omega]
    simp only [pow_succ]
    generalize hx : Real.sqrt (1-l)=x at hs ⊢
    rw [← hs]
    ring

/-- Every actual Nesterov wave is bounded by its exact endpoint value throughout [0,1].
Use: all first-variation kernels are simultaneously maximized at the zero spectral pair.
Article: jacobi, Theorem 5.1.
Proof: the square root lies in [0,1], so its jth power is at most one. Multiply the previously proved sharp Chebyshev bound by this nonnegative factor. -/
theorem nesterovWave_bound (j:ℕ) {l:ℝ} (hl:l∈Icc (0:ℝ) 1) : |nesterovWave j l|≤j+1 := by
  -- The same endpoint bound applies to both factors of the true two-variable insertion kernel.
  have hs0 := Real.sqrt_nonneg (1-l)
  have hs1 : Real.sqrt (1-l)≤1 := (Real.sqrt_le_one).mpr (by linarith [hl.1])
  rw [nesterovWave_chebyshev j hl.2,abs_mul,abs_of_nonneg (pow_nonneg hs0 _)]
  have hU := chebyshev1.abs_U_eval_le j (by rw [abs_of_nonneg hs0]; exact hs1)
  exact (mul_le_mul_of_nonneg_left hU (pow_nonneg hs0 _)).trans
    (by nlinarith [pow_le_one₀ (n := j) hs0 hs1])

/-- All polynomial waves attain the sharp bound at the same zero spectral endpoint.
Use: identifies the exact squared gain after its finite sum is evaluated.
Article: jacobi, Theorem 5.1.
Proof: the Chebyshev formula at the genuine unit argument has value j+1. -/
@[simp] theorem nesterovWave_endpoint (j:ℕ) : nesterovWave j 0=j+1 := by
  rw [nesterovWave_chebyshev j (by norm_num)]
  simp [U_eval_one]

end
end jacobi.Applications

import jacobi.Counterexample.ConstantDriftPolynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: jacobi, Proposition 6.1.
The literal Laguerre Cholesky coefficients sqrt(i+a+1) and sqrt(i)
satisfy the original drift a+1. Their actual product has the stated
Laguerre recurrence diagonal, and the constructed swapped Jacobi chain
attains the exact complete-fibre minimum with this drift.
Source: Szego, Orthogonal Polynomials, Laguerre recurrence matrix.
Use: laguerre_factor_drift and laguerre_chain_minimum specialize the general proved original factorization theorem.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix jacobi.Finite chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- The source's literal positive Laguerre Cholesky diagonal.
Use: laguerre_factor_drift and laguerre_chain_minimum specialize the general proved original factorization theorem.
Article: jacobi, Proposition 6.1.
-/
def laguerreDiagonal (a:ℝ) (i:ℕ) : ℝ := Real.sqrt (i+a+1)

/-- The source's literal Laguerre lower Cholesky coefficient, with its genuine unused zeroth value zero.
Use: laguerre_factor_drift fixes kappa=a+1, including the original zeroth row.
Article: jacobi, Proposition 6.1.
-/
def laguerreLower (i:ℕ) : ℝ := Real.sqrt i

/-- Every genuine Laguerre factor diagonal is positive throughout the complete source order range.
Use: laguerre_chain_minimum discharges every diagonal-sign premise of the exact original finite-fibre minimum theorem.
Article: jacobi, Proposition 6.1.
Proof: the actual square-root argument i+a+1 is strictly positive. -/
theorem laguerreDiagonal_pos {a:ℝ} (ha:-1<a) (i:ℕ) : 0<laguerreDiagonal a i :=
  Real.sqrt_pos.mpr (by linarith [Nat.cast_nonneg (α:=ℝ) i])

/-- Every used interior lower Laguerre factor entry is strictly positive.
Use: laguerre_chain_minimum constructs an actual irreducible attaining Jacobi chain, not merely a reducible limiting matrix.
Article: jacobi, Proposition 6.1.
Proof: square root preserves strict positivity of the genuine positive natural row index. -/
theorem laguerreLower_pos {i:ℕ} (hi : 0 < i) : 0<laguerreLower i :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr hi)

/-- The actual Laguerre factor has exactly the source's positive constant drift a+1 in every original row.
Use: laguerre_chain_minimum instantiates the fully proved constant-drift optimizer without any unproved numerical or factor certificate.
Article: jacobi, Proposition 6.1.
Proof: square the two actual nonnegative square roots and subtract their genuine arguments. -/
theorem laguerre_factor_drift {a:ℝ} (ha:-1<a) (i:ℕ) :
    (laguerreDiagonal a i)^2-(laguerreLower i)^2=a+1 := by
  rw [laguerreDiagonal,laguerreLower,
    Real.sq_sqrt (by linarith [Nat.cast_nonneg (α:=ℝ) i]),Real.sq_sqrt (Nat.cast_nonneg i)]
  ring

/-- The original Laguerre Cholesky product has exactly its printed recurrence diagonal.
Use: identifies the source matrix to which laguerre_chain_minimum applies, retaining the literal original Laguerre normalization.
Article: jacobi, Proposition 6.1.
Source: Szego, Orthogonal Polynomials, Laguerre recurrence matrix.
Proof: the earlier exact bidiagonal product formula gives d_i^2+l_i^2
in every positive row and only d_0^2 at zero. The actual square roots
give the displayed value in both original boundary cases. -/
theorem laguerre_matrix_diagonal {N:ℕ} {a:ℝ} (ha:-1<a) (i:Fin N) :
    (bidiagonal (laguerreDiagonal a) laguerreLower N*
      (bidiagonal (laguerreDiagonal a) laguerreLower N)ᵀ) i i=2*(i:ℝ)+a+1 := by
  -- The original finite zeroth-row convention is kept explicitly.
  rw [bidiagonal,Bidiagonal.mul_transpose_apply,ite_eq_left rfl]
  rw [laguerreDiagonal,Real.sq_sqrt (by linarith [Nat.cast_nonneg (α:=ℝ) i.val])]
  by_cases hi : 0 < i.val
  · rw [ite_eq_left hi,laguerreLower,Real.sq_sqrt (Nat.cast_nonneg i.val)]
    ring
  · have hi0 : i.val=0 := by omega
    rw [ite_eq_right hi,hi0]
    norm_num

/-- The actual Laguerre-factor attaining chain reaches the exact source minimum over its complete positive-coupling isospectral fibre.
Use: Proposition 6.1 applies this fully discharged exact finite minimum at the original H_n.
Article: jacobi, Proposition 6.1.
Proof: substitute the source's literal square-root factor. The zeroth
lower entry is zero, all actual used signs are proved strict, and the
complete original drift identity is a theorem. The general attained
minimum therefore applies with kappa=a+1. -/
theorem laguerre_chain_minimum {N:ℕ} (hN:0<N) {a H:ℝ} (ha:-1<a) (hH:0<H) :
    InFiber (constantDriftChain (laguerreDiagonal a) laguerreLower N H)
      (constantDriftChain (laguerreDiagonal a) laguerreLower N H).matrix.charpoly ∧
    (constantDriftChain (laguerreDiagonal a) laguerreLower N H).energy=(N:ℝ)*H^2/(a+1)^2 ∧
    ∀J:Jacobi N,InFiber J
      (constantDriftChain (laguerreDiagonal a) laguerreLower N H).matrix.charpoly →
        (N:ℝ)*H^2/(a+1)^2≤J.energy :=
  constantDriftChain_minimum hN (laguerreDiagonal a) laguerreLower
    (by linarith) hH (by simp only [laguerreLower,Nat.cast_zero,Real.sqrt_zero])
    (fun i _=>laguerreDiagonal_pos ha i) (fun _ hi _=>laguerreLower_pos hi)
    (fun i _=>laguerre_factor_drift ha i)

end
end jacobi.Counterexample

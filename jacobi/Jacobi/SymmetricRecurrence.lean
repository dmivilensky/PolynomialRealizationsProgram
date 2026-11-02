import jacobi.Jacobi.SymmetricLadder

/-!
Article: jacobi, Proposition A.1.
The actual symmetric Jacobi family has its exact degree recurrence,
proved from its already formalized polynomial equation and endpoint
normalization. No independent recurrence is postulated for the family.
Use: SymmetricCoordinate and NesterovIdentification connect this same
source family to the original general-momentum iteration.
Source: classical Jacobi/Gegenbauer degree recurrence, DLMF 18.9.1.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Raising the actual endpoint-normalized symmetric Jacobi polynomial gives precisely its next genuine degree with the exact classical coefficient.
Use: symmetric_degree_recurrence eliminates the derivative between the actual raising and lowering identities.
Article: jacobi, Proposition A.1.
Proof: the exact ladder algebra gives the same next-degree original equation. Both actual polynomials have endpoint value n+2*alpha+1, so the already proved coefficient uniqueness identifies them without any degree premise. -/
theorem symmetric_raise_eq {a:ℝ} (ha:-1<a) (n:ℕ) :
    C ((n:ℝ)+2*a+1)*shiftedPolynomial a a (n+1)=
      symmetricRaise a n (shiftedPolynomial a a n) := by
  -- Uniqueness is for the actual original differential equation, including all possible polynomial degrees.
  apply Eq.symm
  apply equation_unique ha (n+1)
  · exact symmetric_raise_residual a n _ (shiftedPolynomial_residual ha n)
  · rw [equationResidual_const_mul,shiftedPolynomial_residual ha,mul_zero]
  · simp [symmetricRaise,shiftedPolynomial_zero]

/-- Lowering the actual next symmetric Jacobi polynomial gives exactly n+1 times its genuine predecessor.
Use: symmetric_degree_recurrence obtains the actual original three-term recurrence with its true endpoint normalization.
Article: jacobi, Proposition A.1.
Proof: the genuine lowering residual vanishes by the independently proved actual next-degree equation. Its endpoint value agrees with (n+1)*P_n, so all-degree coefficient uniqueness gives literal polynomial equality. -/
theorem symmetric_lower_eq {a:ℝ} (ha:-1<a) (n:ℕ) :
    C ((n:ℝ)+1)*shiftedPolynomial a a n=
      symmetricLower n (shiftedPolynomial a a (n+1)) := by
  apply Eq.symm
  apply equation_unique ha n
  · exact symmetric_lower_residual a n _ (shiftedPolynomial_residual ha (n+1))
  · rw [equationResidual_const_mul,shiftedPolynomial_residual ha,mul_zero]
  · simp [symmetricLower,shiftedPolynomial_zero]

/-- The genuine normalized symmetric Jacobi polynomials satisfy their exact original degree recurrence.
Use: after the affine x=1-2*t substitution this is the same normalized Gegenbauer recurrence used by the actual Nesterov iteration.
Article: jacobi, Proposition A.1.
Source: the classical symmetric Jacobi recurrence, proved here from the original polynomial equation.
Proof: add the true raising identity at degree n+1 to the true lowering identity from that same degree. Their derivative terms cancel exactly, leaving the original three-term identity with all classical normalizations. -/
theorem symmetric_degree_recurrence {a:ℝ} (ha:-1<a) (n:ℕ) :
    C ((n:ℝ)+2*a+2)*shiftedPolynomial a a (n+2)=
      C (2*(n:ℝ)+2*a+3)*(1-2*X)*shiftedPolynomial a a (n+1)-
        C ((n:ℝ)+1)*shiftedPolynomial a a n := by
  -- The derivative cancellation takes place in the literal polynomial ring, before any evaluation or asymptotic limit.
  have hr:=symmetric_raise_eq ha (n+1)
  have hl:=symmetric_lower_eq ha n
  simp only [Nat.cast_add,Nat.cast_one,symmetricRaise,symmetricLower] at hr hl
  linear_combination (norm := (simp only [map_add,map_mul,map_one,map_ofNat]; ring)) hr+hl

end
end jacobi.Jacobi

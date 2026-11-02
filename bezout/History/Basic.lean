import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
Article: bezout, Section 2 and Theorem 2.1 (causal histories).
Use: the finite lower-triangular solve defines the physical oracle response,
nominal queries and terminal of every unrestricted scalar linear history.
Proof: well-founded recursion on the call index and finite matrix algebra.
-/

namespace bezout

open scoped BigOperators Polynomial
noncomputable section

/-- The coefficients of an N-call history. The strict triangular condition
means that query s can use only answers already returned by the oracle.
Article: bezout, Equation (3). Use: causal execution and the Bezoutian theorem. -/
structure History (N : ℕ) where
  a : Fin N → Fin N → ℝ
  b : Fin N → ℝ
  triangular : ∀ s j, s ≤ j → a s j = 0

namespace History

variable {N : ℕ}

/-- The unique causal solution of a triangular system, written without a
matrix inverse. Article: bezout, Appendix A. Use: polynomial resolvents. -/
def lowerSolve {R : Type*} [Ring R] (A : Fin N → Fin N → R)
    (v : Fin N → R) (s : Fin N) : R :=
  v s - ∑ j : Fin N, if _h : j < s then A s j * lowerSolve A v j else 0
termination_by s.val

/-- The defining row equation of the causal solve.
Article: bezout, Appendix A. Use: inverse and uniqueness identities. -/
theorem lowerSolve_eq {R : Type*} [Ring R] (A : Fin N → Fin N → R)
    (v : Fin N → R) (s : Fin N) :
    lowerSolve A v s =
      v s - ∑ j : Fin N, if j < s then A s j * lowerSolve A v j else 0 := by
  rw [lowerSolve]
  simp only [dite_eq_ite]

/-- Causal row equations determine the whole vector uniquely.
Article: bezout, Theorem 2.1. Use: reconstruction from a normalized basis. -/
theorem lowerSolve_unique {R : Type*} [Ring R] (A : Fin N → Fin N → R)
    (v z : Fin N → R)
    (hz : ∀ s, z s = v s - ∑ j : Fin N, if j < s then A s j * z j else 0) :
    z = lowerSolve A v := by
  funext s
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    rw [hz s, lowerSolve_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < s
    · simp [hj, ih j hj]
    · simp [hj]

/-- The polynomial coefficient of the triangular gradient system.
Article: bezout, Appendix A. Use: the finite polynomial inverse. -/
def coefficient (h : History N) : Fin N → Fin N → ℝ[X] :=
  fun s j => Polynomial.X * Polynomial.C (h.a s j)

/-- The causal polynomial inverse of I+XA, obtained one column at a time.
Article: bezout, Appendix A. Use: nominal queries and physical responses. -/
def resolvent (h : History N) : Fin N → Fin N → ℝ[X] :=
  fun s j => lowerSolve (fun s j => h.coefficient s j) (fun k => if k = j then 1 else 0) s

/-- Nominal query polynomial. Article: bezout, Theorem 2.1.
Use: the graded normalized query basis associated with a physical history. -/
def query (h : History N) (s : Fin N) : ℝ[X] :=
  ∑ j, h.resolvent s j

/-- The physical response of the terminal to the error in oracle call j.
Article: bezout, Theorem 2.1. Use: all finite-energy and MSE bounds. -/
def response (h : History N) (j : Fin N) : ℝ[X] :=
  - ∑ s, Polynomial.C (h.b s) * h.resolvent s j

/-- Terminal residual polynomial, with exactly the physical output weights.
Article: bezout, Theorem 2.1. Use: the Chebyshev-exact comparison class. -/
def terminal (h : History N) : ℝ[X] :=
  1 - Polynomial.X * ∑ s, Polynomial.C (h.b s) * h.query s

end History
end
end bezout

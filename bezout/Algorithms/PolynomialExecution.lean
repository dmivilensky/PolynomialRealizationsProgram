import bezout.Algorithms.Tape
import Mathlib.Algebra.Algebra.Bilinear

/-!
Article: bezout, verification of Algorithms 1--2 in Appendices B--C.
Use: exact symbolic nominal runs identify the actual causal query and terminal
polynomials of a normalized in-place program. The all-oracle-stream tape theorem
then transports their proved scalar histories to every physical execution.
-/

namespace bezout.Algorithms

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- Evaluation at multiplication by X is the regular polynomial representation.
Use: symbolic nominal register runs recover genuine history polynomials. -/
theorem polynomial_regular_action (p q : ℝ[X]) :
    (aeval (LinearMap.mulLeft ℝ (X : ℝ[X])) p) q = p * q := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp [hp, hr, add_mul]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp [Module.End.mul_apply, LinearMap.pow_mulLeft, Algebra.smul_def, mul_assoc]

namespace RegisterProgram
variable {r N : ℕ}

/-- The actual symbolic query of a normalized program is its induced history polynomial. -/
theorem polynomial_query (program : RegisterProgram r N) (hn : program.TranslationNormalized)
    (s : Fin N) :
    program.queryAt (fun (_ : Fin N) (p : ℝ[X]) => X * p) 1 s = (program.history hn).query s := by
  rw [program.query_eq_history hn]
  have he : (program.history hn).oracleQuery (1 : ℝ[X]) (fun _ p => X * p) s =
      ((program.history hn).run (LinearMap.mulLeft ℝ X) 1 (fun _ => 0)).query s := by
    unfold bezout.History.oracleQuery
    have ha := (program.history hn).oracleAnswers_linear (LinearMap.mulLeft ℝ X)
      (1 : ℝ[X]) (fun _ => 0)
    simp only [LinearMap.mulLeft_apply, add_zero] at ha
    rw [ha]
    rfl
  rw [he, bezout.History.nominal_query, polynomial_regular_action, mul_one]

/-- The actual symbolic output of a normalized program is its induced terminal polynomial. -/
theorem polynomial_output (program : RegisterProgram r N) (hn : program.TranslationNormalized) :
    program.output (fun (_ : Fin N) (p : ℝ[X]) => X * p) 1 = (program.history hn).terminal := by
  rw [program.output_eq_history hn]
  have he := (program.history hn).oracleOutput_linear (LinearMap.mulLeft ℝ X)
    (1 : ℝ[X]) (fun _ => 0)
  simpa only [LinearMap.mulLeft_apply, add_zero, bezout.History.nominal_output,
    polynomial_regular_action, mul_one] using he

end RegisterProgram
end
end bezout.Algorithms

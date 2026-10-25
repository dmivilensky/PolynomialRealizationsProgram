import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic

/-!
Article: the P5 dual factorization at its two double contact points.
Use: exact continuous quadratic residual coefficients for the local branch.
Proof: the double roots give a quartic divisor; the degree bound leaves a
quadratic quotient, whose three coefficients are recovered without division.
-/

noncomputable section
namespace polyak.Boundary.P5
open Polynomial

/-- Article: a vanishing value and first derivative produce a double factor. -/
theorem square_factor_of_value_derivative {P : ℝ[X]} {x : ℝ}
    (hx : P.eval x=0) (hdx : P.derivative.eval x=0) : (X-C x)^2 ∣ P := by
  obtain ⟨Q,hQ⟩ := dvd_iff_isRoot.mpr hx
  have hq : Q.eval x=0 := by
    rw [hQ,derivative_mul] at hdx
    simpa using hdx
  obtain ⟨R,hR⟩ := dvd_iff_isRoot.mpr hq
  refine ⟨R,?_⟩
  rw [hQ,hR]
  ring

/-- Article: the two distinct double contacts yield the full quartic divisor. -/
theorem quartic_factor_of_contacts {P : ℝ[X]} {x y : ℝ} (hxy : x≠y)
    (hx : P.eval x=0) (hdx : P.derivative.eval x=0)
    (hy : P.eval y=0) (hdy : P.derivative.eval y=0) :
    (X-C x)^2*(X-C y)^2 ∣ P := by
  have hc := isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit
  exact (hc.pow (m:=2) (n:=2)).mul_dvd (square_factor_of_value_derivative hx hdx)
    (square_factor_of_value_derivative hy hdy)

/-- Article: after the quartic factor, a sextic dual has a quadratic quotient. -/
theorem exists_quadratic_contact_quotient {P : ℝ[X]} {x y : ℝ} (hP : P.natDegree≤6)
    (hxy : x≠y) (hx : P.eval x=0) (hdx : P.derivative.eval x=0)
    (hy : P.eval y=0) (hdy : P.derivative.eval y=0) :
    ∃ a b c : ℝ, P=(X-C x)^2*(X-C y)^2*(C a*X^2+C b*X+C c) := by
  obtain ⟨Q,hQ⟩ := quartic_factor_of_contacts hxy hx hdx hy hdy
  have hdeg : Q.natDegree≤2 := by
    by_cases hq : Q=0
    · simp [hq]
    have hf : (X-C x)^2*(X-C y)^2 ≠ (0 : ℝ[X]) := by
      exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero x)) (pow_ne_zero _ (X_sub_C_ne_zero y))
    rw [hQ,natDegree_mul hf hq,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero x))
      (pow_ne_zero _ (X_sub_C_ne_zero y)),natDegree_pow,natDegree_pow,natDegree_X_sub_C,
      natDegree_X_sub_C] at hP
    omega
  refine ⟨Q.coeff 2,Q.coeff 1,Q.coeff 0,?_⟩
  rw [hQ]
  congr 1
  have hs := Q.as_sum_range_C_mul_X_pow' (show Q.natDegree<3 by omega)
  simpa [Finset.sum_range_succ,add_assoc,add_comm,add_left_comm] using hs

/-- Article: the leading three coefficients of the two-contact factorization. -/
theorem contact_product_coefficients (a b c x y : ℝ) :
    let P : ℝ[X] := (X-C x)^2*(X-C y)^2*(C a*X^2+C b*X+C c)
    P.coeff 6=a ∧ P.coeff 5=b-2*(x+y)*a ∧
      P.coeff 4=c-2*(x+y)*b+(x^2+4*x*y+y^2)*a := by
  dsimp only
  refine ⟨?_,?_,?_⟩ <;> norm_num [pow_two,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ,coeff_add,coeff_sub,coeff_C,coeff_X]
  <;> ring

/-- Article: the exact residual quadratic of a sextic dual with two double contacts.
This also covers the zero polynomial and every degree below six. -/
theorem hermite_sextic_factor {P : ℝ[X]} {x y : ℝ} (hP : P.natDegree≤6)
    (hxy : x≠y) (hx : P.eval x=0) (hdx : P.derivative.eval x=0)
    (hy : P.eval y=0) (hdy : P.derivative.eval y=0) :
    P=(X-C x)^2*(X-C y)^2*
      (C (P.coeff 6)*X^2+C (P.coeff 5+2*(x+y)*P.coeff 6)*X+
        C (P.coeff 4+2*(x+y)*P.coeff 5+(3*x^2+4*x*y+3*y^2)*P.coeff 6)) := by
  obtain ⟨a,b,c,hfactor⟩ := exists_quadratic_contact_quotient hP hxy hx hdx hy hdy
  obtain ⟨ha,hb,hc⟩ := contact_product_coefficients a b c x y
  rw [← hfactor] at ha hb hc
  have hb' : P.coeff 5+2*(x+y)*P.coeff 6=b := by rw [ha,hb]; ring
  have hc' : P.coeff 4+2*(x+y)*P.coeff 5+(3*x^2+4*x*y+3*y^2)*P.coeff 6=c := by
    rw [ha,hb,hc]
    ring
  rw [hc',hb',ha]
  exact hfactor

/-- Article: the exact evaluated P5 Hermite factor, with its source coefficients. -/
theorem hermite_sextic_eval {P : ℝ[X]} {x y : ℝ} (hP : P.natDegree≤6)
    (hxy : x≠y) (hx : P.eval x=0) (hdx : P.derivative.eval x=0)
    (hy : P.eval y=0) (hdy : P.derivative.eval y=0) (z : ℝ) :
    P.eval z=(z-x)^2*(z-y)^2*(P.coeff 6*z^2+
      (P.coeff 5+2*(x+y)*P.coeff 6)*z+P.coeff 4+2*(x+y)*P.coeff 5+
      (3*x^2+4*x*y+3*y^2)*P.coeff 6) := by
  have he := congrArg (fun Q : ℝ[X] => Q.eval z) (hermite_sextic_factor hP hxy hx hdx hy hdy)
  simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C,eval_add,add_assoc] using he

end polyak.Boundary.P5

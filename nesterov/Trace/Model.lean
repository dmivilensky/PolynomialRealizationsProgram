import nesterov.Stationary.SourceDictionary
import nesterov.Phase.Algebra
import Mathlib.Algebra.Polynomial.Reverse

/-! The literal limiting stationary method and characteristic trace symbol. -/
namespace nesterov.Trace
noncomputable section
open Polynomial Complex

def eval (p : Polynomial ℝ) (z : ℂ) : ℂ := (p.map Complex.ofRealHom).eval z

@[simp] theorem eval_one (p : Polynomial ℝ) : eval p 1=(p.eval 1:ℝ) := by
  simp [eval,Polynomial.eval_map]

@[simp] theorem eval_zero (p : Polynomial ℝ) : eval p 0=(p.coeff 0:ℝ) := by
  simp [eval,←Polynomial.coeff_zero_eq_eval_zero]

@[simp] theorem eval_add (p q : Polynomial ℝ) (z : ℂ) : eval (p+q) z=eval p z+eval q z := by simp [eval]
@[simp] theorem eval_sub (p q : Polynomial ℝ) (z : ℂ) : eval (p-q) z=eval p z-eval q z := by simp [eval]
@[simp] theorem eval_mul (p q : Polynomial ℝ) (z : ℂ) : eval (p*q) z=eval p z*eval q z := by simp [eval]
@[simp] theorem eval_neg (p : Polynomial ℝ) (z : ℂ) : eval (-p) z= -eval p z := by simp [eval]
@[simp] theorem eval_X (z : ℂ) : eval (X : Polynomial ℝ) z=z := by simp [eval]
@[simp] theorem eval_C (a : ℝ) (z : ℂ) : eval (C a) z=(a:ℂ) := by simp [eval]
@[simp] theorem eval_pow (p : Polynomial ℝ) (n : ℕ) (z : ℂ) : eval (p^n) z=eval p z^n := by simp [eval]

structure DoubleRootData where
  method : StationaryMethod
  q : Polynomial ℝ
  y : ℝ
  y_pos : 0<y
  factor : method.recurrencePolynomial=(X-C 1)^2*q
  q_one : q.eval 1= -1/y

namespace DoubleRootData
variable (A : DoubleRootData)

abbrev u : Polynomial ℝ := A.method.queryPolynomial
abbrev v : Polynomial ℝ := A.method.recurrencePolynomial

def phi (lam : ℝ) : Polynomial ℝ := C lam*A.u-A.v

def symbol (ω : ℝ) : ℝ :=
  let z := Complex.exp ((ω:ℂ)*Complex.I)
  ((1-z)*eval (A.phi 0) z*star (eval (A.phi 1) z)).re

def effectiveLead : ℝ := A.u.derivative.eval 1-1+A.y*A.q.derivative.eval 1

def tmmTransfer : Prop := A.u=(C 1-C 3*X)*A.q

@[simp] theorem u_one : A.u.eval 1=1 := by
  simp only [u,StationaryMethod.queryPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    one_pow,mul_one]
  exact A.method.query_sum

@[simp] theorem v_one : A.v.eval 1=0 := by
  simp only [v,StationaryMethod.recurrencePolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    one_pow,mul_one]
  exact A.method.recurrence_sum

@[simp] theorem phi_one (lam : ℝ) : (A.phi lam).eval 1=lam := by simp [phi]

@[simp] theorem eval_phi (lam : ℝ) (z : ℂ) :
    eval (A.phi lam) z= -A.method.characteristic lam z := by
  rw [A.method.characteristic_eq_polynomial_eval]
  simp only [phi,eval,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  change (lam:ℂ)*eval A.u z-eval A.v z= -(eval A.v z-(lam:ℂ)*eval A.u z)
  ring

theorem q_ne_zero : A.q≠0 := by
  intro hq
  have hh := A.q_one
  rw [hq,Polynomial.eval_zero] at hh
  exact (div_ne_zero (by norm_num : (-1:ℝ)≠0) (ne_of_gt A.y_pos)) hh.symm

theorem v_ne_zero : A.v≠0 := by
  apply Polynomial.leadingCoeff_ne_zero.mp
  simpa only [v,A.method.recurrencePolynomial_leadingCoeff] using A.method.leading_ne

theorem phi_natDegree (lam : ℝ) : (A.phi lam).natDegree=A.method.memory := by
  have hu : (C lam*A.u).natDegree<A.v.natDegree := by
    rw [A.method.recurrencePolynomial_natDegree]
    exact (Polynomial.natDegree_C_mul_le _ _).trans_lt A.method.queryPolynomial_natDegree_lt
  rw [phi,Polynomial.natDegree_sub_eq_right_of_natDegree_lt hu,A.method.recurrencePolynomial_natDegree]

theorem phi_leadingCoeff (lam : ℝ) : (A.phi lam).leadingCoeff= -A.v.leadingCoeff := by
  have hu : (C lam*A.u).natDegree<A.v.natDegree := by
    rw [A.method.recurrencePolynomial_natDegree]
    exact (Polynomial.natDegree_C_mul_le _ _).trans_lt A.method.queryPolynomial_natDegree_lt
  apply Polynomial.leadingCoeff_sub_of_degree_lt'
  rw [Polynomial.degree_eq_natDegree A.v_ne_zero]
  exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hu)

end DoubleRootData
end
end nesterov.Trace

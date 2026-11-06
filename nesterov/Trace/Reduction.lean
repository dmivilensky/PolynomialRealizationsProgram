import nesterov.Trace.Model
import nesterov.Trace.BoundaryAlgebra
import nesterov.Stationary.FromPolynomials
import Mathlib.RingTheory.EuclideanDomain

/-! Remove common independent modes without changing the slow step or transfer
function. The reduced data again define a genuine stationary executor. -/
namespace nesterov.Trace
noncomputable section
open Polynomial

structure CommonReduction (A : DoubleRootData) where
  reduced : DoubleRootData
  common : Polynomial ℝ
  common_one : common.eval 1=1
  u_factor : A.u=common*reduced.u
  v_factor : A.v=common*reduced.v
  q_factor : A.q=common*reduced.q
  step_eq : reduced.y=A.y
  coprime : IsCoprime reduced.u reduced.v

namespace DoubleRootData
variable (A : DoubleRootData)

theorem exists_commonReduction : Nonempty (CommonReduction A) := by
  let r := GCDMonoid.gcd A.u A.v
  have hr0 : r≠0 := gcd_ne_zero_of_right A.v_ne_zero
  have hru : r∣A.u := GCDMonoid.gcd_dvd_left _ _
  have hrv : r∣A.v := GCDMonoid.gcd_dvd_right _ _
  let U := A.u/r
  let V := A.v/r
  have hu : r*U=A.u := EuclideanDomain.mul_div_cancel' hr0 hru
  have hv : r*V=A.v := EuclideanDomain.mul_div_cancel' hr0 hrv
  have hr1 : r.eval 1≠0 := by
    intro hh
    have he := congrArg (Polynomial.eval (1:ℝ)) hu
    rw [Polynomial.eval_mul,hh,zero_mul,A.u_one] at he
    norm_num at he
  have hnot : ¬(X-C (1:ℝ))∣r := by
    intro hd
    exact hr1 ((Polynomial.dvd_iff_isRoot).mp hd)
  have hcop : IsCoprime r ((X-C (1:ℝ))^2) :=
    (irreducible_X_sub_C (1:ℝ)).coprime_pow_of_not_dvd 2 hnot
  have hrq : r∣A.q := hcop.dvd_of_dvd_mul_right (by
    change r∣A.q*(X-C 1)^2
    rw [mul_comm,←A.factor]
    exact hrv)
  let Q := A.q/r
  have hq : r*Q=A.q := EuclideanDomain.mul_div_cancel' hr0 hrq
  have hU0 : U≠0 := by
    intro hh
    have he := congrArg (Polynomial.eval (1:ℝ)) hu
    rw [hh,mul_zero,Polynomial.eval_zero,A.u_one] at he
    norm_num at he
  have hV0 : V≠0 := right_div_gcd_ne_zero A.v_ne_zero
  have hV : V=(X-C 1)^2*Q := by
    apply mul_left_cancel₀ hr0
    calc
      r*V = A.v := hv
      _ = (X-C 1)^2*A.q := A.factor
      _ = r*((X-C 1)^2*Q) := by rw [←hq];ring
  let u := C (r.eval 1)*U
  let v := C (r.eval 1)*V
  let q := C (r.eval 1)*Q
  let R := C ((r.eval 1)⁻¹)*r
  have hR1 : R.eval 1=1 := by
    dsimp [R]
    rw [Polynomial.eval_mul,Polynomial.eval_C,inv_mul_cancel₀ hr1]
  have hRu : A.u=R*u := by
    dsimp [R,u]
    calc
      A.u = r*U := hu.symm
      _ = C ((r.eval 1)⁻¹)*r*(C (r.eval 1)*U) := by
        rw [mul_assoc _ r _,mul_left_comm r (C _),←mul_assoc,←C_mul,inv_mul_cancel₀ hr1,C_1,one_mul]
  have hRv : A.v=R*v := by
    dsimp [R,v]
    calc
      A.v = r*V := hv.symm
      _ = C ((r.eval 1)⁻¹)*r*(C (r.eval 1)*V) := by
        rw [mul_assoc _ r _,mul_left_comm r (C _),←mul_assoc,←C_mul,inv_mul_cancel₀ hr1,C_1,one_mul]
  have hRq : A.q=R*q := by
    dsimp [R,q]
    calc
      A.q = r*Q := hq.symm
      _ = C ((r.eval 1)⁻¹)*r*(C (r.eval 1)*Q) := by
        rw [mul_assoc _ r _,mul_left_comm r (C _),←mul_assoc,←C_mul,inv_mul_cancel₀ hr1,C_1,one_mul]
  have hu1 : u.eval 1=1 := by
    have hh := congrArg (Polynomial.eval (1:ℝ)) hRu
    simpa only [Polynomial.eval_mul,hR1,one_mul,A.u_one] using hh.symm
  have hv1 : v.eval 1=0 := by
    have hh := congrArg (Polynomial.eval (1:ℝ)) hRv
    simpa only [Polynomial.eval_mul,hR1,one_mul,A.v_one] using hh.symm
  have hv0 : v≠0 := mul_ne_zero (C_ne_zero.mpr hr1) hV0
  have hdeg : u.natDegree<v.natDegree := by
    have hh := A.method.queryPolynomial_natDegree_lt
    rw [←A.method.recurrencePolynomial_natDegree] at hh
    change A.u.natDegree<A.v.natDegree at hh
    rw [←hu,←hv,natDegree_mul hr0 hU0,natDegree_mul hr0 hV0] at hh
    dsimp [u,v]
    rw [natDegree_C_mul hr1,natDegree_C_mul hr1]
    omega
  let M := StationaryMethod.ofPolynomials u v hu1 hv1 hv0 hdeg
  have hfactor : M.recurrencePolynomial=(X-C 1)^2*q := by
    rw [StationaryMethod.ofPolynomials_recurrence]
    dsimp [v,q]
    rw [hV]
    ring
  have hq1 : q.eval 1= -1/A.y := by
    have hh := congrArg (Polynomial.eval (1:ℝ)) hRq
    simpa only [Polynomial.eval_mul,hR1,one_mul,A.q_one] using hh.symm
  let B : DoubleRootData := ⟨M,q,A.y,A.y_pos,hfactor,hq1⟩
  have hcopUV : IsCoprime u v := by
    have hh : IsCoprime U V := isCoprime_div_gcd_div_gcd A.v_ne_zero
    obtain ⟨a,b,hab⟩ := hh
    refine ⟨C ((r.eval 1)⁻¹)*a,C ((r.eval 1)⁻¹)*b,?_⟩
    dsimp [u,v]
    calc
      _ = C ((r.eval 1)⁻¹)*C (r.eval 1)*(a*U+b*V) := by ring
      _ = 1 := by rw [hab,mul_one,←C_mul,inv_mul_cancel₀ hr1,C_1]
  refine ⟨⟨B,R,hR1,?_,?_,hRq,rfl,?_⟩⟩
  · simpa only [DoubleRootData.u,B,M,StationaryMethod.ofPolynomials_query] using hRu
  · simpa only [DoubleRootData.v,B,M,StationaryMethod.ofPolynomials_recurrence] using hRv
  · simpa only [DoubleRootData.u,DoubleRootData.v,B,M,StationaryMethod.ofPolynomials_query,StationaryMethod.ofPolynomials_recurrence] using hcopUV

end DoubleRootData
end
end nesterov.Trace

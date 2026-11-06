import nesterov.Stationary.SourceDictionary
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! A literal stationary executor from consistent explicit coefficient polynomials.
This also permits cancellation of independent common modes in trace arguments. -/
namespace nesterov.StationaryMethod
noncomputable section
open Polynomial
open scoped BigOperators

def ofPolynomials (u v : Polynomial ℝ) (hu : u.eval 1=1) (hv : v.eval 1=0)
    (hv0 : v≠0) (hdeg : u.natDegree<v.natDegree) : StationaryMethod where
  memory := v.natDegree
  memory_pos := Nat.zero_le u.natDegree |>.trans_lt hdeg
  queryCoeff j := u.coeff j.val
  recurrenceCoeff j := v.coeff j.val
  query_sum := by
    rw [Fin.sum_univ_eq_sum_range]
    have hh := Polynomial.eval_eq_sum_range' hdeg (1:ℝ)
    simpa only [hu,one_pow,mul_one] using hh.symm
  recurrence_sum := by
    rw [Fin.sum_univ_eq_sum_range]
    have hh := Polynomial.eval_eq_sum_range' (Nat.lt_succ_self v.natDegree) (1:ℝ)
    simpa only [hv,one_pow,mul_one] using hh.symm
  leading_ne := by
    rw [Fin.val_last,Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hv0

@[simp] theorem ofPolynomials_query (u v : Polynomial ℝ) (hu : u.eval 1=1) (hv : v.eval 1=0)
    (hv0 : v≠0) (hdeg : u.natDegree<v.natDegree) :
    (ofPolynomials u v hu hv hv0 hdeg).queryPolynomial=u := by
  change (∑ j : Fin v.natDegree,Polynomial.monomial j.val (u.coeff j.val))=u
  exact (Fin.sum_univ_eq_sum_range (fun i=>Polynomial.monomial i (u.coeff i)) v.natDegree).trans
    (Polynomial.as_sum_range' u v.natDegree hdeg).symm

@[simp] theorem ofPolynomials_recurrence (u v : Polynomial ℝ) (hu : u.eval 1=1) (hv : v.eval 1=0)
    (hv0 : v≠0) (hdeg : u.natDegree<v.natDegree) :
    (ofPolynomials u v hu hv hv0 hdeg).recurrencePolynomial=v := by
  change (∑ j : Fin (v.natDegree+1),Polynomial.monomial j.val (v.coeff j.val))=v
  exact (Fin.sum_univ_eq_sum_range (fun i=>Polynomial.monomial i (v.coeff i)) (v.natDegree+1)).trans
    (Polynomial.as_sum_range' v (v.natDegree+1) (Nat.lt_succ_self _)).symm

end
end nesterov.StationaryMethod

import nesterov.Stationary.Polynomial

/-!
Article: Definition `def:slm` and the characteristic polynomials in §§4–5.
Use: the finite coefficient executor and the article's literal polynomials
are linked by exact coefficient, degree, normalization and evaluation identities.
The executor uses v−λu; the article's φλ=λu−v differs only by a minus sign.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open Polynomial
variable (M : nesterov.StationaryMethod)

@[simp] theorem queryPolynomial_one : M.queryPolynomial.eval 1=1 := by
  simpa only [queryPolynomial,eval_finsetSum,eval_monomial,one_pow,mul_one] using M.query_sum

@[simp] theorem recurrencePolynomial_one : M.recurrencePolynomial.eval 1=0 := by
  simpa only [recurrencePolynomial,eval_finsetSum,eval_monomial,one_pow,mul_one] using M.recurrence_sum

theorem queryPolynomial_ne_zero : M.queryPolynomial≠0 := by
  intro hz
  have hh := M.queryPolynomial_one
  rw [hz,eval_zero] at hh
  norm_num at hh

theorem queryPolynomial_coeff (j : Fin M.memory) : M.queryPolynomial.coeff j.val=M.queryCoeff j := by
  classical
  simp only [queryPolynomial,finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact ite_eq_right (fun hval => hb (Fin.ext hval))
  · simp

theorem recurrencePolynomial_coeff (j : Fin (M.memory+1)) :
    M.recurrencePolynomial.coeff j.val=M.recurrenceCoeff j := by
  classical
  simp only [recurrencePolynomial,finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact ite_eq_right (fun hval => hb (Fin.ext hval))
  · simp

theorem queryPolynomial_degree_lt : M.queryPolynomial.degree<M.memory := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n hn
  simp only [queryPolynomial,finsetSum_coeff,coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (by omega)

theorem queryPolynomial_natDegree_lt : M.queryPolynomial.natDegree<M.memory :=
  (natDegree_lt_iff_degree_lt M.queryPolynomial_ne_zero).mpr M.queryPolynomial_degree_lt

theorem recurrencePolynomial_natDegree : M.recurrencePolynomial.natDegree=M.memory := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    simp only [recurrencePolynomial,finsetSum_coeff,coeff_monomial]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (by omega)
  · have hh : M.recurrencePolynomial.coeff M.memory=M.recurrenceCoeff (Fin.last M.memory) :=
      M.recurrencePolynomial_coeff (Fin.last M.memory)
    rw [hh]
    exact M.leading_ne

theorem recurrencePolynomial_leadingCoeff :
    M.recurrencePolynomial.leadingCoeff=M.recurrenceCoeff (Fin.last M.memory) := by
  change M.recurrencePolynomial.coeff M.recurrencePolynomial.natDegree=_
  rw [M.recurrencePolynomial_natDegree]
  exact M.recurrencePolynomial_coeff (Fin.last M.memory)

/-- Actual complex evaluation of the literal query polynomial. -/
theorem queryPolynomial_complex_eval (z : ℂ) :
    (M.queryPolynomial.map Complex.ofRealHom).eval z=
      ∑ j : Fin M.memory,(M.queryCoeff j:ℂ)*z^j.val := by
  simp only [queryPolynomial,eval_map,eval₂_finsetSum,eval₂_monomial ]
  rfl

/-- Actual complex evaluation of the literal recursion polynomial. -/
theorem recurrencePolynomial_complex_eval (z : ℂ) :
    (M.recurrencePolynomial.map Complex.ofRealHom).eval z=
      ∑ j : Fin (M.memory+1),(M.recurrenceCoeff j:ℂ)*z^j.val := by
  simp only [recurrencePolynomial,eval_map,eval₂_finsetSum,eval₂_monomial ]
  rfl

theorem characteristic_eq_polynomial_eval (lam : ℝ) (z : ℂ) :
    M.characteristic lam z=
      ((M.recurrencePolynomial.map Complex.ofRealHom)-
        C (lam:ℂ)*(M.queryPolynomial.map Complex.ofRealHom)).eval z := by
  simp only [eval_sub,eval_mul,eval_C,M.recurrencePolynomial_complex_eval,
    M.queryPolynomial_complex_eval,characteristic]

theorem characteristicPolynomial_eq_source (lam : ℝ) :
    M.characteristicPolynomial lam=
      (M.recurrencePolynomial.map Complex.ofRealHom)-
        C (lam:ℂ)*(M.queryPolynomial.map Complex.ofRealHom) := by
  apply Polynomial.funext
  intro z
  rw [M.characteristicPolynomial_eval,M.characteristic_eq_polynomial_eval]

/-- The article's φλ=λu−v and the executor have exactly the same roots. -/
theorem source_characteristic_root_iff (lam : ℝ) (z : ℂ) :
    (C (lam:ℂ)*(M.queryPolynomial.map Complex.ofRealHom)-
      (M.recurrencePolynomial.map Complex.ofRealHom)).eval z=0 ↔
      M.characteristic lam z=0 := by
  rw [M.characteristic_eq_polynomial_eval]
  simp only [eval_sub,eval_mul,eval_C,sub_eq_zero]
  exact eq_comm

end
end nesterov.StationaryMethod

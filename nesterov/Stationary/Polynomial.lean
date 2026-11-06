import nesterov.Stationary.Model
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Article: Definition `def:slm` and the quadratic lower bound in Lemma `lem:envelope`.
Use: original scalar characteristic roots and a nonzero quadratic mode for every
consistent finite-memory method. Common roots and unstable methods are allowed.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open Polynomial
variable (M : nesterov.StationaryMethod)

/-- v(z)−λu(z), in ascending coefficient order. -/
def characteristic (lam : ℝ) (z : ℂ) : ℂ :=
  (∑ j : Fin (M.memory+1), (M.recurrenceCoeff j:ℂ)*z^j.val) -
    (lam:ℂ)*(∑ j : Fin M.memory, (M.queryCoeff j:ℂ)*z^j.val)

/-- Polynomial representation retaining the literal nonzero leading coefficient. -/
def characteristicPolynomial (lam : ℝ) : Polynomial ℂ :=
  (∑ j : Fin M.memory, monomial j.val
    ((M.recurrenceCoeff j.castSucc:ℂ)-(lam:ℂ)*(M.queryCoeff j:ℂ))) +
    monomial M.memory (M.recurrenceCoeff (Fin.last M.memory):ℂ)

theorem characteristicPolynomial_eval (lam : ℝ) (z : ℂ) :
    (M.characteristicPolynomial lam).eval z = M.characteristic lam z := by
  simp only [characteristicPolynomial,eval_add,eval_finsetSum,eval_monomial,characteristic]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
  have hv : (∑ j : Fin M.memory, (M.recurrenceCoeff j.castSucc:ℂ)*z^j.val) =
      ∑ j : Fin M.memory, z^j.val*(M.recurrenceCoeff j.castSucc:ℂ) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hv]
  simp only [mul_assoc]
  abel

theorem characteristic_one (lam : ℝ) : M.characteristic lam 1 = -(lam:ℂ) := by
  have hv : (∑ j, (M.recurrenceCoeff j:ℂ)) = 0 := by
    exact_mod_cast M.recurrence_sum
  have hu : (∑ j, (M.queryCoeff j:ℂ)) = 1 := by exact_mod_cast M.query_sum
  simp [characteristic,hv,hu]

theorem characteristicPolynomial_coeff_top (lam : ℝ) :
    (M.characteristicPolynomial lam).coeff M.memory =
      (M.recurrenceCoeff (Fin.last M.memory):ℂ) := by
  classical
  simp only [characteristicPolynomial,coeff_add,finsetSum_coeff,coeff_monomial]
  have hzero (j : Fin M.memory) :
      (if j.val=M.memory then
        (M.recurrenceCoeff j.castSucc:ℂ)-(lam:ℂ)*(M.queryCoeff j:ℂ) else 0) = 0 := by
    rw [ite_eq_right (ne_of_lt j.isLt)]
  simp only [hzero,Finset.sum_const_zero,↓reduceIte,zero_add]

theorem characteristicPolynomial_natDegree (lam : ℝ) :
    (M.characteristicPolynomial lam).natDegree = M.memory := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    simp only [characteristicPolynomial,coeff_add,finsetSum_coeff,coeff_monomial]
    have hzero (j : Fin M.memory) :
        (if j.val=n then
          (M.recurrenceCoeff j.castSucc:ℂ)-(lam:ℂ)*(M.queryCoeff j:ℂ) else 0)=0 := by
      rw [ite_eq_right (by omega)]
    simp only [hzero,Finset.sum_const_zero,ite_eq_right (by omega : M.memory≠n),add_zero]
  · rw [M.characteristicPolynomial_coeff_top]
    exact Complex.ofReal_ne_zero.mpr M.leading_ne

theorem characteristicPolynomial_leadingCoeff (lam : ℝ) :
    (M.characteristicPolynomial lam).leadingCoeff =
      (M.recurrenceCoeff (Fin.last M.memory):ℂ) := by
  change (M.characteristicPolynomial lam).coeff (M.characteristicPolynomial lam).natDegree = _
  rw [M.characteristicPolynomial_natDegree,M.characteristicPolynomial_coeff_top]

/-- A polynomial with no nonzero root has its value at one equal to its
leading coefficient. This consequence avoids any unproved root enumeration. -/
theorem eval_one_eq_leadingCoeff_of_roots_zero (p : Polynomial ℂ)
    (h : ∀ z : ℂ,p.eval z=0 → z=0) : p.eval 1=p.leadingCoeff := by
  have hp := (IsAlgClosed.splits p).eval_eq_prod_roots (1:ℂ)
  have hprod : (p.roots.map (fun z => (1:ℂ)-z)).prod = 1 := by
    apply Multiset.prod_eq_one
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    have hzroot : p.eval z=0 := (mem_roots (ne_zero_of_mem_roots hz)).mp hz
    rw [h z hzroot]
    simp
  simpa only [hprod,mul_one] using hp

/-- At least one endpoint quadratic has a nonzero characteristic root. -/
theorem exists_nonzero_characteristic_root {μ L : ℝ} (hμL : μ<L) :
    ∃ lam ∈ Set.Icc μ L, ∃ z : ℂ,z≠0 ∧ M.characteristic lam z=0 := by
  by_contra! hn
  have hp (lam : ℝ) (hlam : lam∈Set.Icc μ L) :
      -(lam:ℂ)=(M.recurrenceCoeff (Fin.last M.memory):ℂ) := by
    have hh := eval_one_eq_leadingCoeff_of_roots_zero (M.characteristicPolynomial lam)
      (fun z hz => by
        have hr : M.characteristic lam z=0 := by rwa [M.characteristicPolynomial_eval] at hz
        by_contra hz0
        exact hn lam hlam z hz0 hr)
    simpa only [M.characteristicPolynomial_eval,M.characteristic_one,
      M.characteristicPolynomial_leadingCoeff] using hh
  have hm := hp μ ⟨le_rfl,hμL.le⟩
  have hL := hp L ⟨hμL.le,le_rfl⟩
  have hc : (μ:ℂ)=(L:ℂ) := by linear_combination hL-hm
  exact hμL.ne (Complex.ofReal_injective hc)

end
end nesterov.StationaryMethod

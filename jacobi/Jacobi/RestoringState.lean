import jacobi.Jacobi.FrequencyComparison
import jacobi.Oscillation.PhaseZeros
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Article: jacobi, Proposition B.1.
The original Liouville wave and its actual derivative form a nonvanishing
two-dimensional state on the entire physical interval. Its ordinary phase
therefore exists as the true normalized-state integral. Nontriviality is
proved from actual polynomial root simplicity, including all alpha,beta>-1.
Use: rules out a zero two-dimensional Liouville state and hence constructs the true finite Jacobi phase without a nontriviality premise.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Polynomial MeasureTheory jacobi.Oscillation
set_option backward.isDefEq.respectTransparency false

/-- An actual zero of the shifted Jacobi polynomial has nonzero actual polynomial derivative.
Use: rules out a zero two-dimensional Liouville state and hence constructs the true finite Jacobi phase without a nontriviality premise.
Article: jacobi, Proposition B.1.
Proof: the proved complete polynomial root multiset is duplicate-free.
A common zero of the polynomial and its derivative would have multiplicity
at least two, contradicting that genuine root multiplicity bound. -/
theorem shifted_root_derivative_ne_zero {a b z : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (hz : (shiftedPolynomial a b n).eval z=0) :
    (shiftedPolynomial a b n).derivative.eval z≠0 := by
  -- The polynomial used here is the original finite Jacobi polynomial, whose root count and simplicity were proved by positive-weight orthogonality.
  let p := shiftedPolynomial a b n
  have hp : p≠0 := shiftedPolynomial_ne_zero ha hb n
  have hm : p.rootMultiplicity z≤1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp (shiftedPolynomial_roots ha hb n).2.1 z
  intro hd
  have htwo : 1<p.rootMultiplicity z := (lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).mpr (by
    intro m hm'
    interval_cases m
    · simpa only [Function.iterate_zero,Function.id_def,Polynomial.IsRoot] using hz
    · simpa only [Function.iterate_one,Polynomial.IsRoot] using hd)
  omega

/-- The actual Jacobi Liouville wave and its actual slope never vanish together in the original physical angle interval.
Use: proves the genuine positive phase amplitude for all source parameters, without an assumed ordinary-phase certificate.
Article: jacobi, Proposition B.1.
Proof: the positive Liouville weight reduces a wave zero to an original
polynomial zero. Its derivative is nonzero by actual root simplicity;
the interior sine and weight factors in the original slope are positive. -/
theorem liouville_state_nonzero {a b t : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ)
    (ht : t∈Ioo 0 Real.pi) : liouville a b n t≠0 ∨ liouvilleSlope a b n t≠0 := by
  -- The literal source derivative at a zero loses its logarithmic term, leaving only positive factors times the genuine polynomial derivative.
  by_cases hz : liouville a b n t=0
  · right
    have hw := liouvilleWeight_pos a b ht
    have hangular : angular a b n t=0 := (mul_eq_zero.mp hz).resolve_left hw.ne'
    have hp : (shiftedPolynomial a b n).eval ((1-cos t)/2)=0 := hangular
    have hs : 0<sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    rw [liouvilleSlope,hangular,mul_zero,add_zero,angularSlope]
    exact mul_ne_zero hw.ne' (mul_ne_zero (div_pos hs (by norm_num)).ne'
      (shifted_root_derivative_ne_zero ha hb n hp))
  · exact Or.inl hz

/-- The actual finite Jacobi Liouville wave with every restoring-state input proved on its full physical interval.
Use: its true ordinary phase and exact original zero increments feed the quantitative uniform both-edge zero estimates.
Article: jacobi, Proposition B.1.
-/
def restoringState (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    RestoringSolution (Ioo (0:ℝ) Real.pi) where
  value := liouville a b n
  slope := liouvilleSlope a b n
  potential := fun t => frequency a b n^2+endpointCorrection a/t^2+regularPotential a b t
  value_measurable := by
    unfold liouville liouvilleWeight angular
    fun_prop
  slope_measurable := by
    unfold liouvilleSlope liouvilleWeight liouvilleLogSlope angular angularSlope
    fun_prop
  potential_measurable := by
    have hr : Measurable (regularPotential a b) := measurable_deriv _
    fun_prop
  potential_continuous := by
    intro t ht
    have hr := (regularPotential_analytic a b ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩).1.continuousAt
    have ht0 : t^2≠0 := pow_ne_zero 2 ht.1.ne'
    fun_prop (disch := exact ht0)
  first := fun t ht => liouville_hasDerivAt a b n ht
  second := by
    intro t ht
    convert liouvilleSlope_hasDerivAt a b n ht using 1
    nlinarith [liouville_regular_equation (b := b) ha n ht]
  nontrivial := fun t ht => liouville_state_nonzero ha hb n ht

end
end jacobi.Jacobi

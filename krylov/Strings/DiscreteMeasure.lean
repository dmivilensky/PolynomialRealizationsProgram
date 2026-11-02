import krylov.Strings.DiscreteChristoffel
import krylov.Strings.DiscreteGershgorin
import krylov.Design.AtomicBridge
import Mathlib.MeasureTheory.Measure.Support

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a)`.
Realize the actual finite spectral data as a genuine probability measure
on the real line. Its support is exactly its distinct positive-weight
spectral atoms, and integration is the original weighted spectral sum.
Source: the existing atomic probability bridge and finite Dirac integration.
-/

/-!
Article: krylov, Lemma D.15 [apC:lem:stieltjes].

The actual positive finite path operator has the full simple probability spectrum, polynomial
orthogonality and exact Christoffel kernel; every prescribed nonnegative atomic probability
measure is reconstructed with the stated Robin condition and norm.
Lean uses N+1 masses for article N. The sign-gauged orthogonal-polynomial recurrence gives
positive physical gaps; zero belongs to the spectrum exactly at zero Robin parameter.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Set MeasureTheory Polynomial jacobi.Finite
open scoped BigOperators ENNReal InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- Genuine real probability spectral measure at the unit left mass. -/
def spectralMeasure : ProbabilityMeasure ℝ :=
  krylov.Design.atomicProbability S.spectralData S.spectralData.node

/-- Integration against the actual boundary spectral measure is precisely
the finite positive weighted spectral sum, for every real-valued function. -/
theorem spectralMeasure_integral (f : ℝ→ℝ) :
    (∫ x, f x ∂(S.spectralMeasure : Measure ℝ))=
      ∑ i, S.spectralData.weight i*f (S.spectralData.node i) := by
  change (∫ x, f x ∂∑ i, ENNReal.ofReal (S.spectralData.weight i) •
    Measure.dirac (S.spectralData.node i))=_
  rw [integral_finsetSum_measure (fun i _ ↦
    (integrable_dirac (by finiteness)).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (S.spectralData.positive i).le, smul_eq_mul]

/-- Every actual singleton spectral mass equals its genuine squared
boundary eigenvector coordinate. -/
theorem spectralMeasure_singleton (i : Fin (N+1)) :
    (S.spectralMeasure : Measure ℝ) {S.spectralData.node i}=
      ENNReal.ofReal (S.spectralData.weight i) := by
  change (∑ j, ENNReal.ofReal (S.spectralData.weight j) •
    Measure.dirac (S.spectralData.node j)) {S.spectralData.node i}=_
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hn : S.spectralData.node j≠S.spectralData.node i :=
      fun he ↦ hji (S.spectralData.distinct he)
    simp [hn]
  · simp

/-- The actual real measure has exactly the spectral nodes as its support. -/
theorem spectralMeasure_support :
    (S.spectralMeasure : Measure ℝ).support=Set.range S.spectralData.node := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed (Set.finite_range _).isClosed
    rw [mem_ae_iff]
    change (∑ i, ENNReal.ofReal (S.spectralData.weight i) •
      Measure.dirac (S.spectralData.node i)) (Set.range S.spectralData.node)ᶜ=0
    simp
  · rintro x ⟨i, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hx := mem_of_mem_nhds hU
    have hsub : {S.spectralData.node i}⊆U := Set.singleton_subset_iff.mpr hx
    exact (show 0<(S.spectralMeasure : Measure ℝ) {S.spectralData.node i} by
      rw [S.spectralMeasure_singleton]
      exact ENNReal.ofReal_pos.mpr (S.spectralData.positive i)).trans_le (measure_mono hsub)

/-- Exactly N+1 distinct atoms occur; no endpoint weight vanishes. -/
theorem spectralMeasure_support_card :
    (Set.range S.spectralData.node).ncard=N+1 := by
  rw [Set.ncard_range_of_injective S.spectralData.distinct, Nat.card_fin]

/-- The actual real probability spectral measure is supported precisely
inside the physical interval from zero to the genuine operator norm. -/
theorem spectralMeasure_support_subset :
    (S.spectralMeasure : Measure ℝ).support⊆Set.Icc 0 S.spectralRadius := by
  rw [S.spectralMeasure_support]
  rintro x ⟨i,rfl⟩
  exact ⟨krylov.LinearAlgebra.spectralBasis_eigenvalues_nonneg S.spectralBasis
    S.operator_posSemidef i, (S.spectralRadius_isGreatest S.spectralBasis).2 ⟨i,rfl⟩⟩

/-- The genuine norm is itself an actual atom of the same physical
boundary spectral measure, and is its greatest support point. -/
theorem spectralMeasure_support_isGreatest :
    IsGreatest (S.spectralMeasure : Measure ℝ).support S.spectralRadius := by
  rw [S.spectralMeasure_support]
  exact S.spectralRadius_isGreatest S.spectralBasis

/-- Polynomial integration is the true finite spectral Hilbert norm. -/
theorem spectralMeasure_polynomial_energy (P : ℝ[X]) :
    (∫ x, (P.eval x)^2 ∂(S.spectralMeasure : Measure ℝ))=
      ‖S.spectralData.evaluate P‖^2 := by
  rw [S.spectralMeasure_integral, ← real_inner_self_eq_norm_sq, S.spectralData.inner_evaluate]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual physical position polynomials are orthogonal for the true
boundary spectral measure, with precisely the reciprocal mass norms. -/
theorem spectralMeasure_orthogonality (i j : Fin (N+1)) :
    (∫ x, (S.φPolynomial i.val).eval x*(S.φPolynomial j.val).eval x
      ∂(S.spectralMeasure : Measure ℝ))=(if i=j then (S.mass i.val)⁻¹ else 0) := by
  let c (i : Fin (N+1)) := (-1 : ℝ)^i.val*Real.sqrt (S.mass i.val)
  have hc (i : Fin (N+1)) : c i≠0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Real.sqrt_pos.mpr (S.mass_pos i.val (by omega))).ne'
  have horth := S.spectralData.polynomialBasis.inner_eq_ite i j
  rw [← S.spectralData.evaluate_orthogonalPolynomial i,
    ← S.spectralData.evaluate_orthogonalPolynomial j, S.spectralData.inner_evaluate] at horth
  have he : c i*c j*(∫ x, (S.φPolynomial i.val).eval x*(S.φPolynomial j.val).eval x
      ∂(S.spectralMeasure : Measure ℝ))=(if i=j then 1 else 0) := by
    rw [S.spectralMeasure_integral, Finset.mul_sum]
    convert horth using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [S.orthogonalPolynomial_eq i, S.orthogonalPolynomial_eq j]
    simp only [eval_mul, eval_C, c]
    ring
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left (show i=i from rfl)] at he ⊢
    have hs : c i*c i=S.mass i.val := by
      dsimp only [c]
      calc
        _ = ((-1 : ℝ)^i.val)^2*Real.sqrt (S.mass i.val)^2 := by ring
        _ = _ := by rw [alternating_sq, Real.sq_sqrt (S.mass_pos i.val (by omega)).le, one_mul]
    rw [hs] at he
    apply mul_left_cancel₀ (S.mass_pos i.val (by omega)).ne'
    rw [mul_inv_cancel₀ (S.mass_pos i.val (by omega)).ne']
    exact he
  · rw [ite_eq_right hij] at he ⊢
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (hc i) (hc j))

/-- The exterior minimum for the actual real probability measure is exactly
the reciprocal actual physical prefix energy, with its unique optimizer. -/
theorem spectralMeasure_christoffel (m : ℕ) (hm : m≤N) {P : ℝ[X]}
    (hP : P.natDegree≤m) (hP1 : P.eval (-1)=1) :
    (S.K m)⁻¹≤(∫ x, (P.eval x)^2 ∂(S.spectralMeasure : Measure ℝ)) ∧
      ((∫ x, (P.eval x)^2 ∂(S.spectralMeasure : Measure ℝ))=(S.K m)⁻¹ ↔
        P=S.christoffelOptimizer m) := by
  rw [S.spectralMeasure_polynomial_energy]
  exact S.christoffel_minimum m hm hP hP1

end
end krylov.Strings.DiscreteString

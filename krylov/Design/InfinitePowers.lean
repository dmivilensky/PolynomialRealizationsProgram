import krylov.Design.InfiniteFiniteValues
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Article: main_krylov, thm:limit, infinite criteria for every positive gamma.
Use: the genuine all-measures infinite power criterion, its convergence and
its equality with the supremum of the finite optimized criteria.
Source: the actual Chebyshev extremum and geometric exponential domination.
This extends the earlier half-power infrastructure without changing its objects.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory Set jacobi.Young
open scoped Topology BigOperators

/-- The true all-degree Christoffel power response of a probability measure. -/
def infinitePowerObjective (I : chebyshev1.SpectralInterval) (γ : ℝ)
    (ν : ProbabilityMeasure (Spectrum I)) : ℝ :=
  ∑' n : ℕ, (christoffel (n + 1) 0 (spectralCoordinate I) ν) ^ γ

/-- The genuine optimized all-degree criterion for arbitrary positive gamma. -/
def infinitePowerValue (I : chebyshev1.SpectralInterval) (γ : ℝ) : ℝ :=
  sSup (range (infinitePowerObjective I γ))

/-- A common summable exponential envelope for all probability measures. -/
def powerEnvelope (I : chebyshev1.SpectralInterval) (γ : ℝ) (n : ℕ) : ℝ :=
  4 ^ γ * exp ((n : ℝ) * (-2 * γ * designSpacing I))

/-- The hyperbolic secant has its elementary global exponential bound. -/
theorem sech_le_two_exp (x : ℝ) : sech x ≤ 2 * exp (-x) := by
  rw [sech_exp_nome]
  apply div_le_self (by positivity)
  nlinarith [sq_nonneg (exp (-x))]

/-- Every genuine Christoffel power obeys one common exponential envelope. -/
theorem christoffel_power_le_envelope (I : chebyshev1.SpectralInterval) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) (n : ℕ) :
    (christoffel (n + 1) 0 (spectralCoordinate I) ν) ^ γ ≤ powerEnvelope I γ n := by
  let x := ((n + 1 : ℕ) : ℝ) * designSpacing I
  have hC := (chebyshev_design_extremum_sech I (n + 1)).1 ν
  have hsech := pow_le_pow_left₀ (sech_pos x).le (sech_le_two_exp x) 2
  have he : (2 * exp (-x)) ^ 2 = 4 * exp (-2 * x) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num
  have hmajor : christoffel (n + 1) 0 (spectralCoordinate I) ν ≤ 4 * exp (-2 * x) :=
    hC.trans (hsech.trans_eq he)
  calc
    _ ≤ (4 * exp (-2 * x)) ^ γ :=
      Real.rpow_le_rpow (christoffel_nonneg _ _ _ _) hmajor hγ.le
    _ = 4 ^ γ * exp ((-2 * x) * γ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (exp_nonneg _), ← Real.exp_mul]
    _ ≤ powerEnvelope I γ n := by
      unfold powerEnvelope
      apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (Real.rpow_nonneg (by norm_num) _)
      dsimp only [x]
      push_cast
      nlinarith [mul_pos hγ (designSpacing_pos I)]

/-- The common envelope is a convergent geometric series for every gamma>0. -/
theorem powerEnvelope_summable (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    Summable (powerEnvelope I γ) :=
  (Real.summable_exp_nat_mul_iff.mpr (by nlinarith [mul_pos hγ (designSpacing_pos I)])).mul_left _

/-- Every actual infinite power response converges, without a support or
rank restriction on the probability measure. -/
theorem infinitePowerObjective_summable (I : chebyshev1.SpectralInterval) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    Summable (fun n : ℕ ↦ (christoffel (n + 1) 0 (spectralCoordinate I) ν) ^ γ) :=
  Summable.of_nonneg_of_le (fun _ ↦ Real.rpow_nonneg (christoffel_nonneg _ _ _ _) _)
    (christoffel_power_le_envelope I hγ ν) (powerEnvelope_summable I hγ)

/-- Actual infinite criteria are bounded by one finite common envelope sum. -/
theorem infinitePowerObjective_le_envelope (I : chebyshev1.SpectralInterval) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    infinitePowerObjective I γ ν ≤ ∑' n, powerEnvelope I γ n :=
  (infinitePowerObjective_summable I hγ ν).tsum_le_tsum
    (christoffel_power_le_envelope I hγ ν) (powerEnvelope_summable I hγ)

/-- The all-measures infinite power value has a genuine finite upper bound. -/
theorem infinitePowerValue_le_envelope (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    infinitePowerValue I γ ≤ ∑' n, powerEnvelope I γ n :=
  csSup_le ⟨_, lobattoProbability I 0, rfl⟩
    (by rintro _ ⟨ν, rfl⟩; exact infinitePowerObjective_le_envelope I hγ ν)

/-- Every actual infinite criterion lies below its genuine supremum. -/
theorem infinitePowerObjective_le_value (I : chebyshev1.SpectralInterval) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    infinitePowerObjective I γ ν ≤ infinitePowerValue I γ :=
  le_csSup ⟨_, by rintro _ ⟨η, rfl⟩; exact infinitePowerObjective_le_envelope I hγ η⟩ (mem_range_self ν)

/-- The actual optimized infinite criterion is nonnegative. -/
theorem infinitePowerValue_nonneg (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ infinitePowerValue I γ :=
  (tsum_nonneg (fun n : ℕ ↦ Real.rpow_nonneg
    (christoffel_nonneg (n + 1) 0 (spectralCoordinate I) (lobattoProbability I 0)) γ)).trans
    (infinitePowerObjective_le_value I hγ (lobattoProbability I 0))

/-- The finite uniform power criterion is the actual partial sum. -/
theorem uniformPowerObjective_eq_partialSum (I : chebyshev1.SpectralInterval) (M : ℕ) (γ : ℝ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M (fun _ ↦ 1) γ ν =
      ∑ n ∈ Finset.range M, (christoffel (n + 1) 0 (spectralCoordinate I) ν) ^ γ := by
  simp only [intervalObjective, mixedObjective, one_mul]
  exact Fin.sum_univ_eq_sum_range
    (fun n : ℕ ↦ (christoffel (n + 1) 0 (spectralCoordinate I) ν) ^ γ) M

/-- Finite uniform criteria converge to the infinite criterion of the same measure. -/
theorem uniformPowerObjective_tendsto_infinite (I : chebyshev1.SpectralInterval) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    Tendsto (fun M ↦ intervalObjective I M (fun _ ↦ 1) γ ν) atTop
      (𝓝 (infinitePowerObjective I γ ν)) := by
  simp only [uniformPowerObjective_eq_partialSum]
  exact (infinitePowerObjective_summable I hγ ν).hasSum.tendsto_sum_nat

/-- Finite uniform criteria are below the genuine infinite criterion. -/
theorem uniformPowerObjective_le_infinite (I : chebyshev1.SpectralInterval) (M : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M (fun _ ↦ 1) γ ν ≤ infinitePowerObjective I γ ν := by
  rw [uniformPowerObjective_eq_partialSum]
  exact (infinitePowerObjective_summable I hγ ν).sum_le_tsum _
    (fun _ _ ↦ Real.rpow_nonneg (christoffel_nonneg _ _ _ _) _)

/-- Every finite optimized power value lies below the infinite optimum. -/
theorem uniformPowerValue_le_infinite (I : chebyshev1.SpectralInterval) (M : ℕ) {γ : ℝ}
    (hγ : 0 < γ) : optimalValue I M (fun _ ↦ 1) γ ≤ infinitePowerValue I γ :=
  csSup_le ⟨_, lobattoProbability I 0, rfl⟩ (by
    rintro _ ⟨ν, rfl⟩
    exact (uniformPowerObjective_le_infinite I M hγ ν).trans (infinitePowerObjective_le_value I hγ ν))

/-- Every probability measure lies below the genuine finite optimized power value. -/
theorem uniformPowerObjective_le_optimalValue (I : chebyshev1.SpectralInterval) (M : ℕ) {γ : ℝ}
    (hγ : 0 < γ) (ν : ProbabilityMeasure (Spectrum I)) :
    intervalObjective I M (fun _ ↦ 1) γ ν ≤ optimalValue I M (fun _ ↦ 1) γ :=
  le_csSup ⟨(M : ℝ), by
    rintro _ ⟨η, rfl⟩
    simpa only [intervalObjective, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using mixedObjective_le_sum M (fun _ : Fin M ↦ (1 : ℝ))
      (fun _ ↦ zero_le_one) hγ.le 0 (spectralCoordinate I) η⟩ (mem_range_self ν)

/-- The infinite power optimum is exactly the supremum of the finite
optimized problems. No exchange of an attained optimizer and an infinite sum is assumed. -/
theorem infinitePowerValue_eq_finite_supremum (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    infinitePowerValue I γ = sSup (range (fun M ↦ optimalValue I M (fun _ ↦ 1) γ)) := by
  let V := sSup (range (fun M ↦ optimalValue I M (fun _ ↦ 1) γ))
  have hb : BddAbove (range (fun M ↦ optimalValue I M (fun _ ↦ 1) γ)) :=
    ⟨_, by rintro _ ⟨M, rfl⟩; exact uniformPowerValue_le_infinite I M hγ⟩
  apply le_antisymm
  · have hne : (range (infinitePowerObjective I γ)).Nonempty :=
      ⟨_, lobattoProbability I 0, rfl⟩
    apply csSup_le hne
    rintro _ ⟨ν, rfl⟩
    apply le_of_tendsto (uniformPowerObjective_tendsto_infinite I hγ ν)
    exact Eventually.of_forall (fun M ↦ (uniformPowerObjective_le_optimalValue I M hγ ν).trans
      (le_csSup hb (mem_range_self M)))
  · exact csSup_le (range_nonempty _) (by rintro _ ⟨M, rfl⟩; exact uniformPowerValue_le_infinite I M hγ)

/-- At half gamma the new all-power criterion is literally the existing
source half-power objective. -/
theorem infinitePowerObjective_half (I : chebyshev1.SpectralInterval)
    (ν : ProbabilityMeasure (Spectrum I)) :
    infinitePowerObjective I (1 / 2) ν = infiniteHalfObjective I ν := by
  simp only [infinitePowerObjective, infiniteHalfObjective, Real.sqrt_eq_rpow]

/-- The full-power value specializes to the previously proved half-power value. -/
theorem infinitePowerValue_half (I : chebyshev1.SpectralInterval) :
    infinitePowerValue I (1 / 2) = infiniteHalfValue I := by
  have he : infinitePowerObjective I (1 / 2) = infiniteHalfObjective I :=
    funext (infinitePowerObjective_half I)
  rw [infinitePowerValue, he, infiniteHalfValue]

/-- Finite uniform power criteria increase with their degree budget. -/
theorem uniformPowerObjective_monotone (I : chebyshev1.SpectralInterval) (γ : ℝ)
    (ν : ProbabilityMeasure (Spectrum I)) :
    Monotone (fun M ↦ intervalObjective I M (fun _ ↦ 1) γ ν) := by
  intro M N hMN
  simp only [uniformPowerObjective_eq_partialSum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
    (fun _ _ _ ↦ Real.rpow_nonneg (christoffel_nonneg _ _ _ _) _)

/-- The actual finite optimized power values form an increasing sequence. -/
theorem uniformPowerValue_monotone (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    Monotone (fun M ↦ optimalValue I M (fun _ ↦ 1) γ) := by
  intro M N hMN
  have hne : (range (intervalObjective I M (fun _ ↦ 1) γ)).Nonempty :=
    ⟨_, lobattoProbability I 0, rfl⟩
  apply csSup_le hne
  rintro _ ⟨ν, rfl⟩
  exact (uniformPowerObjective_monotone I γ ν hMN).trans
    (uniformPowerObjective_le_optimalValue I N hγ ν)

/-- Optimizing finite degree budgets and then passing to the limit gives
precisely the actual all-degree power optimum for every gamma>0. -/
theorem uniformPowerValue_tendsto_infinite (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun M ↦ optimalValue I M (fun _ ↦ 1) γ) atTop (𝓝 (infinitePowerValue I γ)) := by
  rw [infinitePowerValue_eq_finite_supremum I hγ]
  exact tendsto_atTop_ciSup (uniformPowerValue_monotone I hγ)
    ⟨_, by rintro _ ⟨M, rfl⟩; exact uniformPowerValue_le_infinite I M hγ⟩

end
end krylov.Design

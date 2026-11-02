import krylov.Asymptotics.RecoveryConvergence
import krylov.Asymptotics.DesignUpperBound
import krylov.Strings.DiscreteMeasure

/-!
Article: main_krylov, thm:limit, lower recovery in the original design problem.
Use: the actual finite recovery string supplies a genuine probability
design in the original interval. Positive affine spectral normalization
identifies its complete Christoffel criterion with the true string energy
sum. The variational lower bounds involve the original all-measure optima.
Source: the constructive finite Stieltjes dictionary and the exact affine
Christoffel invariance, not an assumed spectral approximation certificate.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real MeasureTheory Finset
open krylov.Design krylov.Strings jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator

namespace DiscreteString

/-- Move the true string spectrum back from ζ to the original physical λ. -/
def physicalDesignMeasure {N : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) : DiscreteMeasure (N + 1) :=
  DiscreteInverse.affineMeasure S.spectralData I.mu I.mu I.mu_pos

/-- Actual spectral admissibility follows from the genuine operator norm. -/
theorem physicalDesignMeasure_mem {N : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) (hR : S.spectralRadius ≤ I.kappa - 1)
    (i : Fin (N + 1)) : (physicalDesignMeasure S I).node i ∈ Icc I.mu I.L := by
  have hzero := krylov.LinearAlgebra.spectralBasis_eigenvalues_nonneg S.spectralBasis S.operator_posSemidef i
  have htop := ((S.spectralRadius_isGreatest S.spectralBasis).2 ⟨i, rfl⟩).trans hR
  change I.mu * S.spectralData.node i + I.mu ∈ Icc I.mu I.L
  change 0 ≤ S.spectralData.node i at hzero
  change S.spectralData.node i ≤ I.kappa - 1 at htop
  constructor
  · nlinarith [I.mu_pos]
  · have hh := mul_le_mul_of_nonneg_left htop I.mu_pos.le
    have hκ : I.mu * (I.kappa - 1) + I.mu = I.L := by
      change I.mu * (I.L / I.mu - 1) + I.mu = I.L
      rw [div_eq_mul_inv]
      calc
        _ = I.L * (I.mu * I.mu⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ I.mu_pos.ne', mul_one]
    linarith

/-- True Christoffel energies are unchanged by the inverse physical map. -/
theorem physicalDesignMeasure_kernel {N : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) (m : ℕ) (hm : m ≤ N) :
    krylov.Reference.christoffelKernel (physicalDesignMeasure S I) m 0 = S.K m := by
  have hh := DiscreteInverse.christoffelKernel_affine S.spectralData I.mu I.mu I.mu_pos m (-1)
  rw [show I.mu * (-1) + I.mu = 0 by ring] at hh
  exact hh.trans (S.christoffelKernel_eq m hm)

/-- The genuine finite string reward is a lower bound on the original
all-probability-measures design optimum. -/
theorem reward_le_optimalValue {N : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ)
    (hR : S.spectralRadius ≤ I.kappa - 1) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤ optimalValue I N (fun _ ↦ 1) γ := by
  let M := physicalDesignMeasure S I
  have hm := physicalDesignMeasure_mem S I hR
  let ν := atomicProbability M (fun i ↦ (⟨M.node i, hm i⟩ : Spectrum I))
  have he : intervalObjective I N (fun _ ↦ 1) γ ν = ∑ j ∈ range N, S.K (j + 1) ^ (-γ) := by
    unfold intervalObjective mixedObjective
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [one_mul, interval_christoffel_atomic I M hm (by omega),
      physicalDesignMeasure_kernel S I (i.val + 1) (by omega), ← Real.rpow_neg_eq_inv_rpow]
  rw [← he]
  exact uniformPowerObjective_le_optimalValue I N hγ ν

/-- Every larger original cycle budget contains the actual finite recovery
criterion, without requiring an exact prescribed atom count in the candidate. -/
theorem reward_le_optimalValue_of_le {N M : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ)
    (hR : S.spectralRadius ≤ I.kappa - 1) (hNM : N ≤ M) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤ optimalValue I M (fun _ ↦ 1) γ :=
  (reward_le_optimalValue S I hγ hR).trans (uniformPowerValue_monotone I hγ hNM)

theorem reward_le_infinitePowerValue {N : ℕ} (S : krylov.Strings.DiscreteString N)
    (I : chebyshev1.SpectralInterval) {γ : ℝ} (hγ : 0 < γ)
    (hR : S.spectralRadius ≤ I.kappa - 1) :
    (∑ j ∈ range N, S.K (j + 1) ^ (-γ)) ≤ infinitePowerValue I γ :=
  (reward_le_optimalValue S I hγ hR).trans (uniformPowerValue_le_infinite I N hγ)

end DiscreteString
end
end krylov.Asymptotics

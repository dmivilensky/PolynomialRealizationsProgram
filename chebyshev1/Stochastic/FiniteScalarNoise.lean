import chebyshev1.Stochastic.FiniteNoiseMoments
import chebyshev1.Stochastic.ScalarNoise

/-! The variance polynomial on the original probability space, with hypotheses
only for the finitely many random variables used by the run. -/
namespace chebyshev1.Realization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators
variable {ι d Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem finiteScalarNoise_mean (R : Realization ι) (N : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun (fun s : Fin N => z s.val) μ) (hm : ∀ s<N, Measurable (z s))
    (hi : ∀ s<N, Integrable (z s) μ) (hi2 : ∀ s<N, Integrable (fun ω => z s ω^2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1) :
    (∫ ω, R.scalarNoiseOutput N H B e0 z σ ω ∂μ) =
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial N)).mulVec e0) := by
  simp_rw [scalarNoiseOutput_expansion]
  simpa using Stochastic.integral_finiteNoise_sum_upto hz hm hi hi2 hmean hvar
    (Finset.range N).powerset (by simp) (fun S hS => Finset.mem_powerset.mp hS)
    (fun S => σ^S.card • R.scalarNoiseVector N H B e0 S)

theorem finiteScalarNoise_secondMoment (R : Realization ι) (N : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun (fun s : Fin N => z s.val) μ) (hm : ∀ s<N, Measurable (z s))
    (hi : ∀ s<N, Integrable (z s) μ) (hi2 : ∀ s<N, Integrable (fun ω => z s ω^2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1) :
    (∫ ω, ‖R.scalarNoiseOutput N H B e0 z σ ω‖^2 ∂μ) =
      ∑ k∈Finset.range (N+1), σ^(2*k)*R.scalarNoiseEnergy N H B e0 k := by
  simp_rw [scalarNoiseOutput_expansion]
  rw [Stochastic.integral_finiteNoise_sum_norm_sq_upto hz hm hi hi2 hmean hvar _
    (fun S hS => Finset.mem_powerset.mp hS),Finset.sum_powerset]
  apply Finset.sum_congr (by simp)
  intro k _
  rw [scalarNoiseEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨_,hcard⟩ := Finset.mem_powersetCard.mp hS
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hcard,← pow_mul,Nat.mul_comm k 2]

theorem finiteScalarNoise_variance (R : Realization ι) (N : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun (fun s : Fin N => z s.val) μ) (hm : ∀ s<N, Measurable (z s))
    (hi : ∀ s<N, Integrable (z s) μ) (hi2 : ∀ s<N, Integrable (fun ω => z s ω^2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1) :
    (∫ ω, ‖R.scalarNoiseOutput N H B e0 z σ ω-
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial N)).mulVec e0)‖^2 ∂μ) =
      ∑ k∈Finset.range N, σ^(2*(k+1))*R.scalarNoiseEnergy N H B e0 (k+1) := by
  have hfull := R.finiteScalarNoise_secondMoment N H B e0 z σ hz hm hi hi2 hmean hvar
  simp_rw [scalarNoiseOutput_expansion] at hfull ⊢
  have hcenter := Stochastic.integral_finiteNoise_centered_sum_norm_sq_upto
    hz hm hi hi2 hmean hvar (Finset.range N).powerset (by simp)
    (fun S hS => Finset.mem_powerset.mp hS)
    (fun S => σ^S.card • R.scalarNoiseVector N H B e0 S)
  simp only [Finset.card_empty,pow_zero,one_smul] at hcenter
  rw [← scalarNoiseVector_empty R N H B e0,hcenter]
  rw [Stochastic.integral_finiteNoise_sum_norm_sq_upto hz hm hi hi2 hmean hvar _
    (fun S hS => Finset.mem_powerset.mp hS)] at hfull
  have hzterm : ‖σ^(∅ : Finset ℕ).card • R.scalarNoiseVector N H B e0 ∅‖^2 =
      R.scalarNoiseEnergy N H B e0 0 := by simp
  rw [Finset.sum_erase_eq_sub (by simp),hfull,hzterm,Finset.sum_range_succ']
  simp

theorem finiteScalarNoise_variance_leading (R : Realization ι) {N : ℕ} (hN : 0<N)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ)
    (z : ℕ → Ω → ℝ) (σ : ℝ) (hz : iIndepFun (fun s : Fin N => z s.val) μ)
    (hm : ∀ s<N, Measurable (z s)) (hi : ∀ s<N, Integrable (z s) μ)
    (hi2 : ∀ s<N, Integrable (fun ω => z s ω^2) μ)
    (hmean : ∀ s<N, ∫ ω, z s ω ∂μ=0) (hvar : ∀ s<N, ∫ ω, z s ω^2 ∂μ=1) :
    (∫ ω, ‖R.scalarNoiseOutput N H B e0 z σ ω-
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial N)).mulVec e0)‖^2 ∂μ) =
      σ^2*R.scalarNoiseEnergy N H B e0 1+R.scalarNoiseRemainder N H B e0 σ := by
  rw [R.finiteScalarNoise_variance N H B e0 z σ hz hm hi hi2 hmean hvar]
  have hsplit := Finset.sum_range_succ'
    (fun k => σ^(2*(k+1))*R.scalarNoiseEnergy N H B e0 (k+1)) (N-1)
  rw [show N-1+1=N by omega] at hsplit
  rw [hsplit]
  simp only [zero_add,mul_one,scalarNoiseRemainder,Nat.add_assoc]
  exact add_comm _ _

end
end chebyshev1.Realization

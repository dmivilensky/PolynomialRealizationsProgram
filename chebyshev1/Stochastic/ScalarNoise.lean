import chebyshev1.Stochastic.ScalarExpansion
import chebyshev1.Stochastic.IndependentMoments
import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Independent centered scalar Hessian noise: exact mean and the complete
nonnegative polynomial for the terminal centered second moment.
-/
namespace chebyshev1.Realization
noncomputable section
open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators

variable {ι d Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Terminal vector attached to a deterministic subset of noise insertion times. -/
def scalarNoiseVector (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (S : Finset ℕ) : EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((R.scalarNoiseCoefficient n H B S).mulVec e0)

/-- Terminal output for a path of independently sampled scalar Hessian errors. -/
def scalarNoiseOutput (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ) (ω : Ω) :
    EuclideanSpace ℝ d :=
  WithLp.toLp 2 ((R.operatorTransfer n (fun s => H + (σ * z s ω) • B s)).mulVec e0)

omit [MeasurableSpace Ω] in
theorem scalarNoiseOutput_expansion (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ) (ω : Ω) :
    R.scalarNoiseOutput n H B e0 z σ ω =
      ∑ S ∈ (Finset.range n).powerset, Stochastic.finiteNoiseMonomial z S ω •
        (σ ^ S.card • R.scalarNoiseVector n H B e0 S) := by
  rw [scalarNoiseOutput, R.scalarNoise_expansion]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, WithLp.toLp_sum, WithLp.toLp_smul,
    scalarNoiseVector, Stochastic.finiteNoiseMonomial, smul_smul, mul_comm]

@[simp] theorem scalarNoiseVector_empty (R : Realization ι) (n : ℕ)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) :
    R.scalarNoiseVector n H B e0 ∅ =
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial n)).mulVec e0) := by
  simp [scalarNoiseVector]

theorem scalarNoise_mean (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun z μ) (hm : ∀ s, Measurable (z s))
    (hi : ∀ s, Integrable (z s) μ)
    (hmean : ∀ s, ∫ ω, z s ω ∂μ = 0)
    (hvar : ∀ s, ∫ ω, z s ω ^ 2 ∂μ = 1) :
    (∫ ω, R.scalarNoiseOutput n H B e0 z σ ω ∂μ) =
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial n)).mulVec e0) := by
  simp_rw [scalarNoiseOutput_expansion]
  simpa using Stochastic.integral_finiteNoise_sum hz hm hi hmean hvar
    (Finset.range n).powerset (by simp)
    (fun S => σ ^ S.card • R.scalarNoiseVector n H B e0 S)

/-- The coefficient of `σ^(2k)` in the terminal second moment. -/
def scalarNoiseEnergy (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.range n).powersetCard k, ‖R.scalarNoiseVector n H B e0 S‖ ^ 2

theorem scalarNoiseEnergy_nonneg (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (k : ℕ) :
    0 ≤ R.scalarNoiseEnergy n H B e0 k := by
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- All even coefficients, including the deterministic zeroth term, are exact. -/
theorem scalarNoise_secondMoment (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun z μ) (hm : ∀ s, Measurable (z s))
    (hi : ∀ s, Integrable (z s) μ) (hi2 : ∀ s, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s, ∫ ω, z s ω ∂μ = 0)
    (hvar : ∀ s, ∫ ω, z s ω ^ 2 ∂μ = 1) :
    (∫ ω, ‖R.scalarNoiseOutput n H B e0 z σ ω‖ ^ 2 ∂μ) =
      ∑ k ∈ Finset.range (n+1), σ ^ (2*k) * R.scalarNoiseEnergy n H B e0 k := by
  simp_rw [scalarNoiseOutput_expansion]
  rw [Stochastic.integral_finiteNoise_sum_norm_sq hz hm hi hi2 hmean hvar,
    Finset.sum_powerset]
  apply Finset.sum_congr (by simp)
  intro k _
  rw [scalarNoiseEnergy, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨_, hcard⟩ := Finset.mem_powersetCard.mp hS
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hcard, ← pow_mul, Nat.mul_comm k 2]

@[simp] theorem scalarNoiseEnergy_zero (R : Realization ι) (n : ℕ)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) :
    R.scalarNoiseEnergy n H B e0 0 = ‖R.scalarNoiseVector n H B e0 ∅‖ ^ 2 := by
  simp [scalarNoiseEnergy]

/-- Exact centered variance, including every insertion order and a nonnegative coefficient. -/
theorem scalarNoise_variance (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (z : ℕ → Ω → ℝ) (σ : ℝ)
    (hz : iIndepFun z μ) (hm : ∀ s, Measurable (z s))
    (hi : ∀ s, Integrable (z s) μ) (hi2 : ∀ s, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s, ∫ ω, z s ω ∂μ = 0)
    (hvar : ∀ s, ∫ ω, z s ω ^ 2 ∂μ = 1) :
    (∫ ω, ‖R.scalarNoiseOutput n H B e0 z σ ω -
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial n)).mulVec e0)‖ ^ 2 ∂μ) =
      ∑ k ∈ Finset.range n, σ ^ (2*(k+1)) * R.scalarNoiseEnergy n H B e0 (k+1) := by
  have hfull := R.scalarNoise_secondMoment n H B e0 z σ hz hm hi hi2 hmean hvar
  simp_rw [scalarNoiseOutput_expansion] at hfull ⊢
  have hcenter := Stochastic.integral_finiteNoise_centered_sum_norm_sq
    hz hm hi hi2 hmean hvar (Finset.range n).powerset (by simp)
    (fun S => σ ^ S.card • R.scalarNoiseVector n H B e0 S)
  simp only [Finset.card_empty, pow_zero, one_smul] at hcenter
  rw [← scalarNoiseVector_empty R n H B e0, hcenter]
  rw [Stochastic.integral_finiteNoise_sum_norm_sq hz hm hi hi2 hmean hvar] at hfull
  have hzterm : ‖σ ^ (∅ : Finset ℕ).card • R.scalarNoiseVector n H B e0 ∅‖ ^ 2 =
      R.scalarNoiseEnergy n H B e0 0 := by simp
  rw [Finset.sum_erase_eq_sub (by simp), hfull, hzterm,
    Finset.sum_range_succ']
  simp

/-- The order-two coefficient is the sum of squared single-insertion responses. -/
theorem scalarNoiseEnergy_one (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) :
    R.scalarNoiseEnergy n H B e0 1 =
      ∑ s ∈ Finset.range n, ‖R.scalarNoiseVector n H B e0 {s}‖ ^ 2 := by
  simp [scalarNoiseEnergy, Finset.powersetCard_one]

/-- All insertion orders at least two, contributing noise order at least four. -/
def scalarNoiseRemainder (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (σ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n-1), σ ^ (2*(k+2)) * R.scalarNoiseEnergy n H B e0 (k+2)

theorem scalarNoiseRemainder_nonneg (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (σ : ℝ) :
    0 ≤ R.scalarNoiseRemainder n H B e0 σ := by
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg _ (R.scalarNoiseEnergy_nonneg n H B e0 (k+2))
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg σ) (k+2)

theorem scalarNoiseRemainder_factor (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) (σ : ℝ) :
    R.scalarNoiseRemainder n H B e0 σ = σ^4 *
      ∑ k ∈ Finset.range (n-1), σ ^ (2*k) * R.scalarNoiseEnergy n H B e0 (k+2) := by
  rw [scalarNoiseRemainder, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show 2*(k+2) = 4+2*k by omega, pow_add]
  ring

theorem scalarNoiseRemainder_isBigO (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ) :
    (fun σ => R.scalarNoiseRemainder n H B e0 σ) =O[nhds 0] (fun σ : ℝ => σ^4) := by
  have hc : ContinuousAt (fun σ : ℝ =>
      ∑ k ∈ Finset.range (n-1), σ ^ (2*k) * R.scalarNoiseEnergy n H B e0 (k+2)) 0 := by
    fun_prop
  have h := (Asymptotics.isBigO_refl (fun σ : ℝ => σ^4) (nhds 0)).mul
    (hc.isBigO (F := ℝ))
  simpa only [← scalarNoiseRemainder_factor, mul_one] using h

/-- The leading variance and its nonnegative fourth-order remainder. -/
theorem scalarNoise_variance_leading (R : Realization ι) {n : ℕ} (hn : 0 < n)
    (H : Matrix d d ℝ) (B : ℕ → Matrix d d ℝ) (e0 : d → ℝ)
    (z : ℕ → Ω → ℝ) (σ : ℝ) (hz : iIndepFun z μ)
    (hm : ∀ s, Measurable (z s)) (hi : ∀ s, Integrable (z s) μ)
    (hi2 : ∀ s, Integrable (fun ω => z s ω ^ 2) μ)
    (hmean : ∀ s, ∫ ω, z s ω ∂μ = 0)
    (hvar : ∀ s, ∫ ω, z s ω ^ 2 ∂μ = 1) :
    (∫ ω, ‖R.scalarNoiseOutput n H B e0 z σ ω -
      WithLp.toLp 2 ((Polynomial.aeval H (R.residualPolynomial n)).mulVec e0)‖ ^ 2 ∂μ) =
      σ^2 * R.scalarNoiseEnergy n H B e0 1 + R.scalarNoiseRemainder n H B e0 σ := by
  rw [R.scalarNoise_variance n H B e0 z σ hz hm hi hi2 hmean hvar]
  have hsplit := Finset.sum_range_succ'
    (fun k => σ ^ (2*(k+1)) * R.scalarNoiseEnergy n H B e0 (k+1)) (n-1)
  rw [show n-1+1 = n by omega] at hsplit
  rw [hsplit]
  simp only [zero_add, mul_one, scalarNoiseRemainder, Nat.add_assoc]
  exact add_comm _ _

end
end chebyshev1.Realization

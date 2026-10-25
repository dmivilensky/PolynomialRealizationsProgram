import polyak.Levels.Program.Curve
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Full programs with arbitrary signed lag sets and arbitrary finite measures. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace polyak.Levels

def nonzeroLags : Set ℤ := {n | n ≠ 0}

def ProgramSolution (Θ : Curve) (𝒩 : Set ℤ) (w : Measure Frequency) : Prop :=
  IsFiniteMeasure w ∧ w ≠ 0 ∧ 0 ≤ ∫ ω, Θ.minimizer ω ∂w ∧
    ∀ n ∈ 𝒩, 0 ≤ ∫ ω, Θ.lag n ω ∂w

def FPOn (Θ : Curve) (𝒩 : Set ℤ) : Prop := ∃ w, ProgramSolution Θ 𝒩 w
def FP (Θ : Curve) : Prop := FPOn Θ nonzeroLags

def ProbabilitySolution (Θ : Curve) (𝒩 : Set ℤ) (w : ProbabilityMeasure Frequency) : Prop :=
  0 ≤ ∫ ω, Θ.minimizer ω ∂w ∧ ∀ n ∈ 𝒩, 0 ≤ ∫ ω, Θ.lag n ω ∂w

theorem ProgramSolution.relax {Θ : Curve} {𝒩 𝒩' : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) (hsub : 𝒩' ⊆ 𝒩) : ProgramSolution Θ 𝒩' w :=
  ⟨h.1,h.2.1,h.2.2.1,fun n hn => h.2.2.2 n (hsub hn)⟩

theorem FPOn.relax {Θ : Curve} {𝒩 𝒩' : Set ℤ} (h : FPOn Θ 𝒩)
    (hsub : 𝒩' ⊆ 𝒩) : FPOn Θ 𝒩' := by
  rcases h with ⟨w,hw⟩
  exact ⟨w,hw.relax hsub⟩

theorem ProbabilitySolution.toProgramSolution {Θ : Curve} {𝒩 : Set ℤ}
    {w : ProbabilityMeasure Frequency} (h : ProbabilitySolution Θ 𝒩 w) :
    ProgramSolution Θ 𝒩 (w : Measure Frequency) :=
  ⟨inferInstance,MeasureTheory.IsProbabilityMeasure.ne_zero _,h.1,h.2⟩

structure CertificateSymbol (Θ : Curve) (𝒩 : Set ℤ) where
  lags : Finset ℤ
  lags_subset : ∀ n ∈ lags, n ∈ 𝒩
  weight : ℤ → ℝ
  weight_nonneg : ∀ n ∈ lags, 0 ≤ weight n
  gamma : ℝ
  gamma_nonneg : 0 ≤ gamma

def CertificateSymbol.eval {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) (ω : Frequency) : ℝ :=
  (∑ n ∈ S.lags, S.weight n * Θ.lag n ω) + S.gamma * Θ.minimizer ω

theorem CertificateSymbol.continuous_eval {Θ : Curve} {𝒩 : Set ℤ}
    (S : CertificateSymbol Θ 𝒩) : Continuous S.eval := by
  unfold eval
  exact (continuous_finsetSum _ (fun n _ => continuous_const.mul (Θ.continuous_lag n))).add
    (continuous_const.mul Θ.continuous_minimizer)

structure StrictSymbol (Θ : Curve) (𝒩 : Set ℤ) where
  symbol : CertificateSymbol Θ 𝒩
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  strict : ∀ ω, symbol.eval ω ≤ -epsilon

theorem StrictSymbol.gamma_pos {Θ : Curve} {𝒩 : Set ℤ} (S : StrictSymbol Θ 𝒩) :
    0 < S.symbol.gamma := by
  have h := S.strict frequencyZero
  simp only [CertificateSymbol.eval,Curve.lag_at_zero,mul_zero,Finset.sum_const_zero,
    Curve.minimizer_at_zero,mul_neg, mul_one,zero_add] at h
  linarith [S.epsilon_pos]

end polyak.Levels

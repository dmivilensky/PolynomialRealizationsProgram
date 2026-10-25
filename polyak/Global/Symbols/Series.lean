import polyak.Levels.Program.Alternative
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Genuine summable nonnegative signed-lag symbols. The residual mass is
retained in the minimizer coefficient; the series converges uniformly. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Topology
open scoped BigOperators

structure Weights (𝒩 : Set ℤ) where
  weight : ℤ→ℝ
  nonneg : ∀n,0≤weight n
  outside : ∀n,n∉𝒩→weight n=0
  summable : Summable weight
  mass_le_one : ∑'n,weight n≤1

def Weights.gamma {𝒩 : Set ℤ} (a : Weights 𝒩) : ℝ := 1-∑'n,a.weight n

def Weights.series {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (ω : Frequency) : ℝ :=
  ∑'n,a.weight n*Θ.lag n ω

def Weights.eval {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (ω : Frequency) : ℝ :=
  a.series Θ ω+a.gamma*Θ.minimizer ω

theorem Weights.gamma_nonneg {𝒩 : Set ℤ} (a : Weights 𝒩) : 0≤a.gamma :=
  sub_nonneg.mpr a.mass_le_one

theorem Weights.normalized {𝒩 : Set ℤ} (a : Weights 𝒩) :
    (∑'n,a.weight n)+a.gamma=1 := by unfold gamma; ring

theorem lag_norm_le_two (Θ : Curve) (n : ℤ) (ω : Frequency) : ‖Θ.lag n ω‖≤2 := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  dsimp [Curve.lag]
  constructor <;> linarith [Real.neg_one_le_cos (Θ ω),Real.cos_le_one (Θ ω),
    Real.neg_one_le_cos ((n:ℝ)*(ω:ℝ)-Θ ω),Real.cos_le_one ((n:ℝ)*(ω:ℝ)-Θ ω)]

theorem Weights.term_norm_le {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (n : ℤ) (ω : Frequency) :
    ‖a.weight n*Θ.lag n ω‖≤2*a.weight n := by
  rw [norm_mul,Real.norm_of_nonneg (a.nonneg n)]
  nlinarith [lag_norm_le_two Θ n ω,a.nonneg n]

theorem Weights.summable_terms {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) (ω : Frequency) :
    Summable (fun n=>a.weight n*Θ.lag n ω) :=
  (a.summable.mul_left 2).of_norm_bounded (fun n=>a.term_norm_le Θ n ω)

theorem Weights.uniform_series {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) :
    TendstoUniformly (fun F : Finset ℤ=>fun ω=>∑n∈F,a.weight n*Θ.lag n ω)
      (a.series Θ) atTop :=
  tendstoUniformly_tsum (a.summable.mul_left 2) (a.term_norm_le Θ)

theorem Weights.continuous_series {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) :
    Continuous (a.series Θ) :=
  continuous_tsum (fun n=>continuous_const.mul (Θ.continuous_lag n))
    (a.summable.mul_left 2) (a.term_norm_le Θ)

theorem Weights.continuous_eval {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve) :
    Continuous (a.eval Θ) :=
  (a.continuous_series Θ).add (continuous_const.mul Θ.continuous_minimizer)

theorem Weights.integrable_series {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    (w : Measure Frequency) [IsFiniteMeasure w] : Integrable (a.series Θ) w :=
  (a.continuous_series Θ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Weights.integrable_eval {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    (w : Measure Frequency) [IsFiniteMeasure w] : Integrable (a.eval Θ) w :=
  (a.continuous_eval Θ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Weights.integral_eval {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    (w : Measure Frequency) [IsFiniteMeasure w] :
    (∫ω,a.eval Θ ω ∂w)=(∑'n,a.weight n*(∫ω,Θ.lag n ω ∂w))+
      a.gamma*(∫ω,Θ.minimizer ω ∂w) := by
  have hint (n : ℤ) : Integrable (fun ω=>a.weight n*Θ.lag n ω) w :=
    (integrable_curve_lag Θ n w).const_mul _
  have hbound (n : ℤ) : (∫ω,‖a.weight n*Θ.lag n ω‖ ∂w)≤
      (2*a.weight n)*w.real Set.univ := by
    have hh := integral_mono (hint n).norm (integrable_const (2*a.weight n))
      (a.term_norm_le Θ n)
    simpa only [integral_const,smul_eq_mul,mul_comm] using hh
  have hs : Summable (fun n=>∫ω,‖a.weight n*Θ.lag n ω‖ ∂w) :=
    ((a.summable.mul_left 2).mul_right (w.real Set.univ)).of_nonneg_of_le
      (fun n=>integral_nonneg (fun _=>norm_nonneg _)) hbound
  unfold eval
  rw [integral_add (a.integrable_series Θ w)
    ((integrable_curve_minimizer Θ w).const_mul _),integral_const_mul]
  unfold series
  rw [←integral_tsum_of_summable_integral_norm hint hs]
  simp only [integral_const_mul]

end polyak.Global.Symbols

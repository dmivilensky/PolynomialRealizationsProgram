import polyak.Global.Symbols.Series
import Mathlib.MeasureTheory.Measure.Support

/-! Complementary slackness holds for every genuine finite solution of the
full measure program, with no finite-support restriction on either side. -/
noncomputable section
namespace polyak.Global.Symbols
open Levels MeasureTheory Filter Set Topology
open scoped BigOperators

theorem lag_integral_norm_bound (Θ : Curve) (n : ℤ) (w : Measure Frequency)
    [IsFiniteMeasure w] : ‖∫ω,Θ.lag n ω ∂w‖≤2*w.real univ := by
  have hh := integral_mono (integrable_curve_lag Θ n w).norm (integrable_const (2:ℝ))
    (lag_norm_le_two Θ n)
  exact (norm_integral_le_integral_norm _).trans (by simpa only [integral_const,smul_eq_mul,mul_comm] using hh)

theorem Weights.summable_integrals {𝒩 : Set ℤ} (a : Weights 𝒩) (Θ : Curve)
    (w : Measure Frequency) [IsFiniteMeasure w] :
    Summable (fun n=>a.weight n*(∫ω,Θ.lag n ω ∂w)) := by
  apply ((a.summable.mul_left 2).mul_right (w.real univ)).of_norm_bounded
  intro n
  rw [norm_mul,Real.norm_of_nonneg (a.nonneg n)]
  have hh := mul_le_mul_of_nonneg_left (lag_integral_norm_bound Θ n w) (a.nonneg n)
  nlinarith [hh]

theorem Weights.integral_nonneg_of_solution {𝒩 : Set ℤ} (a : Weights 𝒩)
    {Θ : Curve} {w : Measure Frequency} (hw : ProgramSolution Θ 𝒩 w) :
    0≤∫ω,a.eval Θ ω ∂w := by
  let : IsFiniteMeasure w := hw.1
  rw [a.integral_eval Θ w]
  apply add_nonneg
  · apply tsum_nonneg
    intro n
    by_cases hn : n∈𝒩
    · exact mul_nonneg (a.nonneg n) (hw.2.2.2 n hn)
    · rw [a.outside n hn,zero_mul]
  · exact mul_nonneg a.gamma_nonneg hw.2.2.1

theorem Weights.solution_integral_zero {𝒩 : Set ℤ} (a : Weights 𝒩) {Θ : Curve}
    (hS : ∀ω,a.eval Θ ω≤0) {w : Measure Frequency} (hw : ProgramSolution Θ 𝒩 w) :
    (∫ω,a.eval Θ ω ∂w)=0 :=
  le_antisymm (integral_nonpos hS) (a.integral_nonneg_of_solution hw)

theorem Weights.solution_carried_zero {𝒩 : Set ℤ} (a : Weights 𝒩) {Θ : Curve}
    (hS : ∀ω,a.eval Θ ω≤0) {w : Measure Frequency} (hw : ProgramSolution Θ 𝒩 w) :
    ∀ᵐω∂w,a.eval Θ ω=0 := by
  let : IsFiniteMeasure w := hw.1
  have hi := (a.integrable_eval Θ w).neg
  have hz : (∫ω,-a.eval Θ ω ∂w)=0 := by
    rw [integral_neg,a.solution_integral_zero hS hw,neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω=>neg_nonneg.mpr (hS ω)) hi).mp hz
  filter_upwards [hae] with ω hω
  exact neg_eq_zero.mp hω

theorem Weights.solution_support_zero {𝒩 : Set ℤ} (a : Weights 𝒩) {Θ : Curve}
    (hS : ∀ω,a.eval Θ ω≤0) {w : Measure Frequency} (hw : ProgramSolution Θ 𝒩 w) :
    w.support⊆{ω|a.eval Θ ω=0} :=
  w.support_subset_of_isClosed (isClosed_eq (a.continuous_eval Θ) continuous_const)
    (a.solution_carried_zero hS hw)

theorem Weights.complementary_slackness {𝒩 : Set ℤ} (a : Weights 𝒩) {Θ : Curve}
    (hS : ∀ω,a.eval Θ ω≤0) {w : Measure Frequency} (hw : ProgramSolution Θ 𝒩 w) :
    (∀n,0<a.weight n→(∫ω,Θ.lag n ω ∂w)=0) ∧
      (0<a.gamma→(∫ω,Θ.minimizer ω ∂w)=0) := by
  let : IsFiniteMeasure w := hw.1
  have ht (n : ℤ) : 0≤a.weight n*(∫ω,Θ.lag n ω ∂w) := by
    by_cases hn : n∈𝒩
    · exact mul_nonneg (a.nonneg n) (hw.2.2.2 n hn)
    · rw [a.outside n hn,zero_mul]
  have hg : 0≤a.gamma*(∫ω,Θ.minimizer ω ∂w) := mul_nonneg a.gamma_nonneg hw.2.2.1
  have hsum : 0≤∑'n,a.weight n*(∫ω,Θ.lag n ω ∂w) := tsum_nonneg ht
  have he := a.solution_integral_zero hS hw
  rw [a.integral_eval Θ w] at he
  constructor
  · intro n hn
    have hb := (a.summable_integrals Θ w).le_tsum n (fun k _=>ht k)
    have hz : a.weight n*(∫ω,Θ.lag n ω ∂w)=0 := by linarith [ht n]
    exact (mul_eq_zero.mp hz).resolve_left hn.ne'
  · intro hγ
    have hz : a.gamma*(∫ω,Θ.minimizer ω ∂w)=0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hγ.ne'

theorem Weights.max_zero_of_feasible {𝒩 : Set ℤ} (a : Weights 𝒩) {Θ : Curve}
    (hS : ∀ω,a.eval Θ ω≤0) (hFP : FPOn Θ 𝒩) :
    IsGreatest (range (a.eval Θ)) 0 := by
  obtain ⟨w,hw⟩ := hFP
  let : NeZero w := ⟨hw.2.1⟩
  obtain ⟨ω,hω⟩ := (a.solution_carried_zero hS hw).exists
  exact ⟨⟨ω,hω⟩,fun x hx=>by obtain ⟨ω,rfl⟩:=hx; exact hS ω⟩

end polyak.Global.Symbols

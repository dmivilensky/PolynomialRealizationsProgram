import nesterov.Flow.Constants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Article: Appendix B, Equation (AB) and the program P_c.
Use: the exact all-real-lag kernels of the continuous spiral interpolation
problem, including both directions and the minimizer constraint.
-/

noncomputable section

namespace nesterov.Flow

def kernelA (c γ q : ℝ) : ℝ := Real.cosh (c * q) - Real.cos (γ * q)

def kernelB (c γ q : ℝ) : ℝ := γ * Real.sinh (c * q) / c - Real.sin (γ * q)

theorem kernelA_nonneg (c γ q : ℝ) : 0 ≤ kernelA c γ q := by
  dsimp [kernelA]
  linarith [Real.one_le_cosh (c * q), Real.cos_le_one (γ * q)]

theorem kernelA_pos {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (γ : ℝ) :
    0 < kernelA c γ q := by
  have h := Real.one_lt_cosh.mpr (ne_of_gt (mul_pos hc hq))
  dsimp [kernelA]
  linarith [Real.cos_le_one (γ * q)]

theorem kernelB_nonneg {c γ q : ℝ} (hc : 0 < c) (hγ : 0 ≤ γ) (hq : 0 ≤ q) :
    0 ≤ kernelB c γ q := by
  have hs := Real.self_le_sinh_iff.mpr (mul_nonneg hc.le hq)
  have hmul := mul_le_mul_of_nonneg_left hs hγ
  have hsin := Real.sin_le (mul_nonneg hγ hq)
  dsimp [kernelB]
  have hh : γ * q ≤ γ * Real.sinh (c * q) / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  linarith

/-- The two time-direction interpolation slacks of one frequency. -/
def forwardKernel (θ m c γ q : ℝ) : ℝ :=
  (γ ^ 2 - delta θ m c) * kernelA c γ q - (θ - 2 * c) * γ * kernelB c γ q

def backwardKernel (θ m c γ q : ℝ) : ℝ :=
  (γ ^ 2 - delta θ m c) * kernelA c γ q + (θ - 2 * c) * γ * kernelB c γ q

/-- Candidate value of the convex remainder at time zero in one plane. -/
def atomValue (θ m c γ : ℝ) : ℝ :=
  ((θ - c) * γ ^ 2 - c * delta θ m c) / (2 * c)

/-- Candidate support gap against the minimizer in one plane. -/
def atomMinimizerGap (θ m c γ : ℝ) : ℝ :=
  ((3 * c - θ) * γ ^ 2 - c * delta θ m c) / (2 * c)

/-- A finite probability distribution of nonnegative spiral frequencies. -/
structure Spectrum (J : Type*) [Fintype J] where
  frequency : J → ℝ
  weight : J → ℝ
  frequency_nonneg : ∀ j, 0 ≤ frequency j
  weight_nonneg : ∀ j, 0 ≤ weight j
  weight_sum : ∑ j, weight j = 1

variable {J : Type*} [Fintype J]

/-- Program P_c; lags are arbitrary positive reals, not sampled times. -/
def Spectrum.Feasible (ν : Spectrum J) (θ m c : ℝ) : Prop :=
  (∀ q : ℝ, 0 < q → 0 ≤ ∑ j, ν.weight j * forwardKernel θ m c (ν.frequency j) q) ∧
  (∀ q : ℝ, 0 < q → 0 ≤ ∑ j, ν.weight j * backwardKernel θ m c (ν.frequency j) q) ∧
  c * delta θ m c ≤ (3 * c - θ) * ∑ j, ν.weight j * ν.frequency j ^ 2

theorem atomValue_sub_gap {θ m c γ : ℝ} (hc : 0 < c) :
    atomValue θ m c γ - atomMinimizerGap θ m c γ = (θ - 2 * c) * γ ^ 2 / c := by
  dsimp [atomValue, atomMinimizerGap]
  field_simp
  ring

theorem atomValue_add_gap {θ m c γ : ℝ} (hc : 0 < c) :
    atomValue θ m c γ + atomMinimizerGap θ m c γ = γ ^ 2 - delta θ m c := by
  dsimp [atomValue, atomMinimizerGap]
  field_simp
  ring

/-- The minimizer constraint forces c>θ/3 whenever the quadratic mode is
strictly stable.  This is the necessary ceiling mechanism in §3. -/
theorem Spectrum.third_lt_of_feasible {ν : Spectrum J} {θ m c : ℝ}
    (hc : 0 < c) (hd : 0 < delta θ m c) (h : ν.Feasible θ m c) : θ / 3 < c := by
  have hmom : 0 ≤ ∑ j, ν.weight j * ν.frequency j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (ν.weight_nonneg j) (sq_nonneg _)
  have hp := mul_pos hc hd
  by_contra hh
  have hcoef : 3 * c - θ ≤ 0 := by linarith
  have hn := mul_nonpos_of_nonpos_of_nonneg hcoef hmom
  linarith [h.2.2]

end nesterov.Flow

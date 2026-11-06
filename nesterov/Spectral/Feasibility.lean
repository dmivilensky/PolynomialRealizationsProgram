import polyak.Spectral.Coordinates
import polyak.Spectral.GeneralCompact

/-!
The article's division-free two-amplitude spectral program.  In particular,
query zeros and common zeros of the two symbols are retained.
-/

noncomputable section

open MeasureTheory

namespace nesterov.Spectral

abbrev Frequency := polyak.Spectral.Frequency
abbrev Spectrum := polyak.Spectral.Spectrum

/-- The query and normalized-gradient amplitudes, without taking their quotient. -/
structure SymbolPair where
  u : C(Frequency, ℂ)
  p : C(Frequency, ℂ)

def g (a : SymbolPair) (c : Frequency) : ℝ :=
  Complex.normSq (a.u c) - Complex.normSq (a.p c)

def skew (a : SymbolPair) (c : Frequency) : ℝ :=
  (a.p c * star (a.u c)).im

def lagA (a : SymbolPair) (t : ℝ) (n : ℕ) (c : Frequency) : ℝ :=
  g a c * (Real.cosh (n * t) - Real.cos (n * Real.arccos c))

def lagB (a : SymbolPair) (n : ℕ) (c : Frequency) : ℝ :=
  2 * skew a c * Real.sin (n * Real.arccos c)

def meanG (ν : Spectrum) (a : SymbolPair) : ℝ := ∫ c, g a c ∂ν
def meanA (ν : Spectrum) (a : SymbolPair) (t : ℝ) (n : ℕ) : ℝ :=
  ∫ c, lagA a t n c ∂ν
def meanB (ν : Spectrum) (a : SymbolPair) (n : ℕ) : ℝ := ∫ c, lagB a n c ∂ν

/-- Every lag is imposed, together with both inequalities against the minimizer. -/
def Feasible (a : SymbolPair) (t : ℝ) (ν : Spectrum) (C : ℝ) : Prop :=
  |C| ≤ meanG ν a ∧ ∀ n : ℕ, 1 ≤ n →
    0 ≤ meanA ν a t n - meanB ν a n + C * Real.sinh (n * t) ∧
    0 ≤ meanA ν a t n + meanB ν a n - C * Real.sinh (n * t)

theorem continuous_g (a : SymbolPair) : Continuous (g a) := by
  unfold g; fun_prop

theorem continuous_skew (a : SymbolPair) : Continuous (skew a) := by
  unfold skew; fun_prop

theorem continuous_lagA (a : SymbolPair) (t : ℝ) (n : ℕ) :
    Continuous (lagA a t n) := by
  unfold lagA g; fun_prop

theorem continuous_lagB (a : SymbolPair) (n : ℕ) : Continuous (lagB a n) := by
  unfold lagB skew; fun_prop

theorem meanG_le_norm_sq (ν : Spectrum) (a : SymbolPair) : meanG ν a ≤ ‖a.u‖ ^ 2 := by
  have hle (c : Frequency) : g a c ≤ ‖a.u‖ ^ 2 := by
    have hn := a.u.norm_coe_le_norm c
    have hu : Complex.normSq (a.u c) ≤ ‖a.u‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    exact (sub_le_self _ (Complex.normSq_nonneg _)).trans hu
  have h := integral_mono (polyak.Spectral.integrable_continuous ν (continuous_g a))
    (integrable_const (‖a.u‖ ^ 2)) hle
  simpa [meanG] using h

theorem Feasible.abs_C_le {a : SymbolPair} {t C : ℝ} {ν : Spectrum}
    (h : Feasible a t ν C) : |C| ≤ ‖a.u‖ ^ 2 :=
  h.1.trans (meanG_le_norm_sq ν a)

theorem Feasible.meanG_nonneg {a : SymbolPair} {t C : ℝ} {ν : Spectrum}
    (h : Feasible a t ν C) : 0 ≤ meanG ν a := (abs_nonneg C).trans h.1

theorem Feasible.meanA_nonneg {a : SymbolPair} {t C : ℝ} {ν : Spectrum}
    (h : Feasible a t ν C) (n : ℕ) (hn : 1 ≤ n) : 0 ≤ meanA ν a t n := by
  obtain ⟨hl, hu⟩ := h.2 n hn
  linarith

/-- Reversing radial growth reverses the common value charge and preserves both slacks. -/
theorem feasible_neg_t_iff (a : SymbolPair) (t C : ℝ) (ν : Spectrum) :
    Feasible a (-t) ν (-C) ↔ Feasible a t ν C := by
  simp only [Feasible, meanA, lagA, abs_neg, mul_neg, Real.cosh_neg, Real.sinh_neg,
    neg_mul, neg_neg]

end nesterov.Spectral

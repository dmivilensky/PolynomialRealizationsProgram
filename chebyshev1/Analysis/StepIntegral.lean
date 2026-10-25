import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
Article: chebyshev1, Theorem 5.1.
Step Integral.
Use: `chebyshev1.Analysis.uniformStep_integral` feeds
`chebyshev1.SineJacobi.diagonalProfile_square_integral` (diagonal Profile square integral).
Proof chain: `chebyshev1.SineJacobi.sineIntegral_eq` — chebyshev1, Theorem 5.1;
Endpoint-profile L2 convergence and limiting Green energy.
Source: mathlib, Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic,
Mathlib.MeasureTheory.Measure.Lebesgue.Basic — integration of uniform mesh step functions. The
needed form is proved here.
-/
namespace chebyshev1.Analysis
noncomputable section
open Set MeasureTheory
open scoped BigOperators

/--
Defines `uniformStep` of type `(N : ℕ) (a : ℕ → ℝ) (x : ℝ)` by `a (Nat.floor ((N:ℝ)*x))`.

Use: `chebyshev1.Analysis.uniformStep_integral` uses this definition to establish exact
identity `(∫ x in (0:ℝ)..1, uniformStep N a x) = (∑ k ∈ Finset.range N, a k)/(N:ℝ)`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic,
Mathlib.MeasureTheory.Measure.Lebesgue.Basic — integration of uniform mesh step functions.
-/
def uniformStep (N : ℕ) (a : ℕ → ℝ) (x : ℝ) := a (Nat.floor ((N:ℝ)*x))

/--
Exact identity `(∫ x in (0:ℝ)..1, uniformStep N a x) = (∑ k ∈ Finset.range N, a k)/(N:ℝ)`.

Use: `chebyshev1.SineJacobi.convolutionStep_integral` rewrites with this identity to
establish exact identity `(∫ x in (0:ℝ)..1, convolutionStep N s x) = ∑ k ∈ Finset.range (s+1),
ratio N k*ratio N (s-k)`.

Article: chebyshev1, Theorem 5.1 via `chebyshev1.SineJacobi.sineIntegral_eq`.

Source: mathlib, Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic,
Mathlib.MeasureTheory.Measure.Lebesgue.Basic — integration of uniform mesh step functions.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem uniformStep_integral (N : ℕ) (a : ℕ → ℝ) (hN : 0 < N) :
    (∫ x in (0:ℝ)..1, uniformStep N a x) = (∑ k ∈ Finset.range N, a k)/(N:ℝ) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hcell (k : ℕ) :
      (∫ x in (k:ℝ)/N..((k:ℝ)+1)/N, uniformStep N a x) = a k/(N:ℝ) := by
    have hab : (k:ℝ)/N ≤ ((k:ℝ)+1)/N := by
      apply div_le_div_of_nonneg_right _ hNr.le; linarith
    have he : (∫ x in (k:ℝ)/N..((k:ℝ)+1)/N, uniformStep N a x) =
        ∫ _ in (k:ℝ)/N..((k:ℝ)+1)/N, a k := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (((k:ℝ)+1)/N)] with x hx hmem
      rw [uIoc_of_le hab] at hmem
      unfold uniformStep
      congr 1
      apply (Nat.floor_eq_iff (mul_nonneg hNr.le (by
        have : 0 ≤ (k:ℝ)/N := div_nonneg (Nat.cast_nonneg _) hNr.le
        linarith [hmem.1]))).mpr
      constructor
      · have := (div_lt_iff₀ hNr).mp hmem.1
        nlinarith
      · have hlt : x < ((k:ℝ)+1)/N := lt_of_le_of_ne hmem.2 hx
        have := (lt_div_iff₀ hNr).mp hlt
        nlinarith
    rw [he, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hint (k : ℕ) : IntervalIntegrable (uniformStep N a) volume
      ((k:ℝ)/N) (((k:ℝ)+1)/N) := by
    have hab : (k:ℝ)/N ≤ ((k:ℝ)+1)/N :=
      div_le_div_of_nonneg_right (by linarith) hNr.le
    apply (intervalIntegrable_const (c := a k)).congr_uIoo
    intro x hmem
    rw [uIoo_of_le hab] at hmem
    unfold uniformStep
    symm
    congr 1
    have hxp : 0 ≤ x := (div_nonneg (Nat.cast_nonneg k) hNr.le).trans hmem.1.le
    apply (Nat.floor_eq_iff (mul_nonneg hNr.le hxp)).mpr
    constructor
    · have := (div_lt_iff₀ hNr).mp hmem.1; nlinarith
    · have := (lt_div_iff₀ hNr).mp hmem.2; nlinarith
  have hs := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k:ℝ)/N)
    (n := N) (fun k _ => by simpa only [Nat.cast_add, Nat.cast_one] using hint k)
  simp only [Nat.cast_zero, zero_div, div_self hNr.ne'] at hs
  rw [← hs]
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [hcell]
  exact (Finset.sum_div _ _ _).symm

end
end chebyshev1.Analysis

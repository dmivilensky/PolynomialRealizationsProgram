import bezout.Comparisons.Classical.History
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Article: bezout, Appendix B, exterior normalization in the classical variance limit.
Use: the exact Chebyshev denominator ratio has a geometric envelope and a
pointwise limit, making the later infinite-series limit fully justified.
Proof: hyperbolic Chebyshev evaluation and elementary geometric convergence.
-/

namespace bezout.Classical
noncomputable section
open Polynomial Polynomial.Chebyshev Real Filter Topology

/-- Hyperbolic coordinate of the fixed positive spectral interval. -/
def theta (I : chebyshev1.SpectralInterval) : ℝ := Real.arcosh I.eta

/-- The positive geometric decay rate associated with that interval. -/
def decay (I : chebyshev1.SpectralInterval) : ℝ := Real.exp (-theta I)

/-- The exterior coordinate has strictly positive hyperbolic angle. -/
theorem theta_pos (I : chebyshev1.SpectralInterval) : 0 < theta I := Real.arcosh_pos I.eta_gt_one

/-- The decay rate lies strictly between zero and one. -/
theorem decay_mem (I : chebyshev1.SpectralInterval) : 0 < decay I ∧ decay I < 1 :=
  ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (theta_pos I))⟩

/-- Exact denominator formula in powers of the geometric rate. -/
theorem den_decay (I : chebyshev1.SpectralInterval) (n : ℕ) :
    I.den n = (decay I ^ n + (decay I ^ n)⁻¹) / 2 := by
  have hη : Real.cosh (theta I) = I.eta := Real.cosh_arcosh I.eta_gt_one.le
  unfold chebyshev1.SpectralInterval.den
  rw [← hη, T_real_cosh, Int.cast_natCast, Real.cosh_eq]
  have he : decay I ^ n = Real.exp (-((n : ℝ) * theta I)) := by
    rw [← mul_neg, Real.exp_nat_mul]
    rfl
  rw [he, Real.exp_neg, inv_inv]
  ring

/-- Squaring a rate power doubles its natural exponent. -/
theorem decay_pow_two (I : chebyshev1.SpectralInterval) (n : ℕ) :
    decay I ^ (2 * n) = (decay I ^ n) ^ 2 := by rw [Nat.mul_comm, pow_mul]

/-- Exact finite exterior ratio, with no limiting approximation. -/
theorem scaled_den_eq (I : chebyshev1.SpectralInterval) (N k : ℕ) (hk : k ≤ N) :
    I.epsilon N * I.den (N-k) =
      decay I ^ k * (1 + decay I ^ (2*(N-k))) / (1 + decay I ^ (2*N)) := by
  have hq : decay I ≠ 0 := ne_of_gt (decay_mem I).1
  have hp : decay I ^ N = decay I ^ k * decay I ^ (N-k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [chebyshev1.SpectralInterval.epsilon, den_decay, den_decay,
    decay_pow_two, decay_pow_two]
  have hn : 1 + (decay I ^ N) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp [hq]
  rw [hp]
  ring

/-- Every finite ratio has a summable geometric envelope uniform in the horizon. -/
theorem scaled_den_le (I : chebyshev1.SpectralInterval) (N k : ℕ) (hk : k ≤ N) :
    I.epsilon N * I.den (N-k) ≤ 2 * decay I ^ k := by
  rw [scaled_den_eq I N k hk]
  have hp : 0 ≤ decay I ^ k := pow_nonneg (decay_mem I).1.le _
  have hbound : decay I ^ (2*(N-k)) ≤ 1 := pow_le_one₀ (decay_mem I).1.le (decay_mem I).2.le
  have hnon : 0 ≤ decay I ^ (2*N) := pow_nonneg (decay_mem I).1.le _
  have hden : 0 < 1 + decay I ^ (2*N) := by linarith
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- Every fixed reversed prefix coefficient converges to the corresponding geometric power. -/
theorem scaled_den_tendsto (I : chebyshev1.SpectralInterval) (k : ℕ) :
    Tendsto (fun N : ℕ => I.epsilon N * I.den (N-k)) atTop (𝓝 (decay I ^ k)) := by
  have hq := tendsto_pow_atTop_nhds_zero_of_lt_one (decay_mem I).1.le (decay_mem I).2
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop := by
    apply tendsto_atTop_mono (fun N => by omega : ∀ N : ℕ, N ≤ 2*N) tendsto_id
  have htail : Tendsto (fun N : ℕ => 2*(N-k)) atTop atTop :=
    hN.comp (Filter.tendsto_sub_atTop_nat k)
  have h := Tendsto.div (((hq.comp htail).const_add 1).const_mul (decay I ^ k))
    ((hq.comp hN).const_add 1) (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have h' : Tendsto (fun N : ℕ => decay I ^ k * (1 + decay I ^ (2*(N-k))) /
      (1 + decay I ^ (2*N))) atTop (𝓝 (decay I ^ k)) := by
    convert h using 1
    · funext n
      rfl
    · simp only [add_zero, mul_one, div_one]
  apply h'.congr'
  filter_upwards [eventually_ge_atTop k] with N hNk
  exact (scaled_den_eq I N k hNk).symm

end
end bezout.Classical

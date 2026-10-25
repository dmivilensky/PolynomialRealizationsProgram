import polyak.FareyPlateau.FanAnalysis.Feasibility

/-! Conversion of the punctured local analytic estimates into a single integer
order cutoff, simultaneously for the two signed Farey families. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter Set
open scoped Topology

theorem large_order_small_delta {k : ℕ} (hk : 3 ≤ k) {p : ℝ → Prop}
    (hp : ∀ᶠ δ in 𝓝[≠] 0, p δ) :
    ∃ L₀ : ℕ, ∀ P : Fan.Data, P.k = k → (L₀ : ℤ) ≤ P.L → p P.delta := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hp
  obtain ⟨L₀, hL₀⟩ := exists_nat_gt (2 * Real.pi / ((k : ℝ) * ε))
  refine ⟨L₀, fun P hPk hPL => hball ⟨?_, ?_⟩⟩
  · have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hLR : (0 : ℝ) < P.L := by exact_mod_cast (show 0 < P.L by have := P.period_ge; have := P.order_gt; omega)
    have hbound : 2 * Real.pi / ((k : ℝ) * ε) < (P.L : ℝ) :=
      hL₀.trans_le (by exact_mod_cast hPL)
    have hs : |(P.sign : ℝ)| = 1 := by
      rcases P.sign_unit with h | h <;> simp only [h] <;> norm_num
    have hδabs : |P.delta| = 2 * Real.pi / ((k : ℝ) * P.L) := by
      unfold Fan.Data.delta
      rw [abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, hs]
      norm_num only [abs_neg, show |(2 : ℝ)| = 2 by norm_num]
      have hden : |(P.k : ℝ) * P.L| = (k : ℝ) * P.L := by
        rw [hPk, Int.cast_natCast, abs_of_pos (mul_pos hkR hLR)]
      rw [hden, mul_one]
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, hδabs]
    apply (div_lt_iff₀ (mul_pos hkR hLR)).mpr
    have hh := (div_lt_iff₀ (mul_pos hkR hε)).mp hbound
    nlinarith
  · simp only [mem_compl_iff, mem_singleton_iff]
    unfold Fan.Data.delta
    apply div_ne_zero
    · have hs : (P.sign : ℝ) ≠ 0 := by rcases P.sign_unit with h | h <;> simp [h]
      exact mul_ne_zero (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) Real.pi_ne_zero) hs
    · have hkz : (P.k : ℝ) ≠ 0 := by exact_mod_cast (show P.k ≠ 0 by have := P.period_ge; omega)
      have hLz : (P.L : ℝ) ≠ 0 := by exact_mod_cast (show P.L ≠ 0 by have := P.period_ge; have := P.order_gt; omega)
      exact mul_ne_zero hkz hLz

namespace Actual
open General Levels ModeLocking
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem fan_feasible {e : ℝ} (he : e < critical A) :
    ∃ L₀ : ℕ, ∀ P : Fan.Data, P.j = j → P.k = k → (L₀ : ℤ) ≤ P.L →
      ∃ a c : Frequency, (a : ℝ) = P.near ∧ (c : ℝ) = P.far ∧
        ProgramSolution (Geometry.shiftedCurve q (A.edgeShift - e * P.delta^2)) nonzeroLags
          (atomicMeasure ![Real.toNNReal ((k : ℝ) - 1 + correction A * P.delta), 1] ![a, c]) := by
  obtain ⟨L₀, hL₀⟩ := large_order_small_delta A.period_ge (fan_feasible_small A he)
  exact ⟨L₀, fun P hj hk hPL => hL₀ P hk hPL P hj hk rfl⟩

end Actual
end polyak.FareyPlateau.FanAnalysis

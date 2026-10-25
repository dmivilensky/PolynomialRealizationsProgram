import polyak.General.Multipliers.Minimum
import Mathlib.Algebra.Order.Archimedean.Basic

/-! The minimum principle at an isolated boundary pole.  The real part may
blow up positively, but a finite lower bound is enough.  Multiplication of
`exp (-n F)` by the boundary-point factor removes the exceptional point;
ordinary maximum modulus and unbounded powers finish the argument. -/

namespace polyak.General.Multipliers
noncomputable section
open Set Metric Filter Topology

theorem real_nonneg_of_frontier_except {F : ℂ → ℂ} {U : Set ℂ} {p : ℂ}
    (hU : Bornology.IsBounded U) (hd : DifferentiableOn ℂ F U)
    (hc : ContinuousOn F (closure U \ {p})) (hp : p ∉ U)
    (hb : ∀ z ∈ frontier U, z ≠ p → 0 ≤ (F z).re)
    (K D : ℝ) (hD : 0 < D)
    (hbound : ∀ z ∈ closure U, z ≠ p → K ≤ (F z).re)
    (hdiam : ∀ z ∈ closure U, ‖z-p‖ ≤ D)
    {z : ℂ} (hz : z ∈ U) : 0 ≤ (F z).re := by
  have hzp : z ≠ p := fun h => hp (h ▸ hz)
  have haux (n : ℕ) :
      ‖(z-p)*Complex.exp (-(n:ℂ)*F z)‖ ≤ D := by
    let H : ℂ → ℂ := fun w => (w-p)*Complex.exp (-(n:ℂ)*F w)
    have hHc : ContinuousOn H (closure U) := by
      intro w hw
      by_cases hwp : w = p
      · subst w
        rw [Metric.continuousWithinAt_iff]
        intro e he
        let C : ℝ := Real.exp (-(n:ℝ)*K)
        have hC : 0 < C := Real.exp_pos _
        refine ⟨e/C, div_pos he hC, ?_⟩
        intro v hv hdist
        have hnorm : ‖H v‖ ≤ ‖v-p‖*C := by
          by_cases hvp : v = p
          · simp [H, hvp]
          · dsimp only [H]
            rw [norm_mul, Complex.norm_exp]
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply Real.exp_le_exp.mpr
            have hvb := hbound v hv hvp
            simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
              Complex.natCast_im, neg_zero, zero_mul, sub_zero] using
              mul_le_mul_of_nonpos_left hvb (neg_nonpos.mpr (Nat.cast_nonneg n))
        have hsmall : ‖v-p‖*C < e := (lt_div_iff₀ hC).mp (by simpa [dist_eq_norm] using hdist)
        simpa only [H, sub_self, zero_mul, dist_zero_right] using hnorm.trans_lt hsmall
      · have hmem : closure U \ {p} ∈ nhdsWithin w (closure U) := by
          exact inter_mem self_mem_nhdsWithin
            (nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hwp))
        have hFc : ContinuousWithinAt F (closure U) w :=
          (hc w ⟨hw, hwp⟩).mono_of_mem_nhdsWithin hmem
        exact (continuous_id.sub continuous_const).continuousWithinAt.mul
          (Complex.continuous_exp.continuousAt.comp_continuousWithinAt
            (continuousWithinAt_const.mul hFc))
    have hHd : DifferentiableOn ℂ H U := by
      unfold H
      exact (differentiable_id.sub_const p).differentiableOn.mul
        (Complex.differentiable_exp.comp_differentiableOn
          ((differentiable_const (-(n:ℂ))).differentiableOn.mul hd))
    apply Complex.norm_le_of_forall_mem_frontier_norm_le hU ⟨hHd,hHc⟩ _ (subset_closure hz)
    intro w hw
    by_cases hwp : w = p
    · simp [H, hwp, hD.le]
    · dsimp only [H]
      rw [norm_mul, Complex.norm_exp]
      apply (mul_le_mul_of_nonneg_left (show Real.exp (-(n:ℂ)*F w).re ≤ 1 from ?_)
        (norm_nonneg (w-p))).trans
      · simpa using hdiam w hw.1
      · rw [Real.exp_le_one_iff]
        have := mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (Nat.cast_nonneg n : 0 ≤ (n:ℝ))) (hb w hw hwp)
        simpa using this
  by_contra h
  have hneg : (F z).re < 0 := lt_of_not_ge h
  have he : 1 < Real.exp (-(F z).re) := Real.one_lt_exp_iff.mpr (neg_pos.mpr hneg)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (D/‖z-p‖) he
  have hb' := haux n
  rw [norm_mul, Complex.norm_exp] at hb'
  have hexp : Real.exp (-(n:ℂ)*F z).re = Real.exp (-(F z).re)^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
  rw [hexp] at hb'
  have hdist : 0 < ‖z-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have := (div_lt_iff₀ hdist).mp hn
  nlinarith

end
end polyak.General.Multipliers

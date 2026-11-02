import krylov.Asymptotics.RecoveryTypeState
import krylov.Asymptotics.RecoveryNorm

/-!
Article: main_krylov, thm:limit, actual finite recovery convergence.
Use: the source's genuine finite strings recover every compact smooth type
state, with a proved first-order error and the actual right-tail truncation
error. Arbitrary vanishing meshes and grids reaching the endpoint converge;
no reward-convergence or spectral approximation premise is assumed.
Source: the proved state/energy estimates and genuine interval Riemann sums.
-/
namespace krylov.Asymptotics
noncomputable section
open Set Real Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace RecoveryState

/-- The genuine finite physical recovery string of this actual type state. -/
def string {Y h : ℝ} (R : RecoveryState Y) (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) : krylov.Strings.DiscreteString N :=
  recoveryString R.density hh N hNY R.density_pos

/-- The true finite Christoffel power sum of the constructed string. -/
def discreteReward {Y h : ℝ} (R : RecoveryState Y) (γ : ℝ) (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) : ℝ :=
  ∑ j ∈ range N, (R.string hh N hNY).K (j + 1) ^ (-γ)

/-- Truncating a positive-energy continuum reward loses at most the
omitted type length. This includes every endpoint and every γ≥0. -/
theorem reward_tail_bound {Y γ t : ℝ} (R : RecoveryState Y) (hγ : 0 ≤ γ)
    (ht : t ∈ Icc 0 Y) :
    |(∫ y in 0..t, R.energy y ^ (-γ)) - ∫ y in 0..Y, R.energy y ^ (-γ)| ≤ Y - t := by
  have hc : ContinuousOn (fun y ↦ R.energy y ^ (-γ)) (Icc 0 Y) :=
    R.energy_C1.continuousOn.rpow_const (fun y hy ↦
      Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (R.energy_one_le y hy))))
  have h0 : IntervalIntegrable (fun y ↦ R.energy y ^ (-γ)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hc.mono (fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩)
  have h1 : IntervalIntegrable (fun y ↦ R.energy y ^ (-γ)) volume t Y := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.2]
    exact hc.mono (fun x hx ↦ ⟨ht.1.trans hx.1, hx.2⟩)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 h1,
    sub_add_cancel_left, abs_neg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := Y)
    (C := 1) (f := fun y ↦ R.energy y ^ (-γ)) (fun y hy ↦ ?_)
  · simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)] using hb
  · rw [uIoc_of_le ht.2] at hy
    have hym : y ∈ Icc 0 Y := ⟨ht.1.trans hy.1.le, hy.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (by have := R.energy_one_le y hym; linarith) _)]
    exact rpow_le_one_of_one_le_of_nonpos (R.energy_one_le y hym) (neg_nonpos.mpr hγ)

/-- The source's actual recovery power sum approximates the full compact
type reward with a proved O(h) error plus the real grid truncation length. -/
theorem exists_reward_error_bound {Y γ : ℝ} (R : RecoveryState Y) (hY : 0 < Y) (hγ : 0 ≤ γ) :
    ∃ C > (0 : ℝ), ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ N : ℕ, ∀ hNY : (N : ℝ) * h ≤ Y,
      |h * R.discreteReward γ hh N hNY - ∫ y in 0..Y, R.energy y ^ (-γ)| ≤
        C * h + (Y - (N : ℝ) * h) := by
  obtain ⟨C, hC, hbound⟩ := exists_recovery_reward_error_bound hY hγ R.density_pos R.density_C1
    R.position_C1 R.slope_C1 R.energy_C1 R.energy_one_le
    R.position_zero R.slope_zero R.energy_zero
    R.position_derivative R.slope_derivative R.energy_derivative
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ N hNY
  have htail := R.reward_tail_bound hγ (show (N : ℝ) * h ∈ Icc 0 Y from
    ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, hNY⟩)
  exact (abs_sub_le _ (∫ y in 0..(N : ℝ) * h, R.energy y ^ (-γ)) _).trans
    (add_le_add (hbound h hh hh₁ N hNY) htail)

/-- Genuine recovery convergence along any vanishing positive mesh whose
true finite grid endpoint tends to the prescribed type endpoint. -/
theorem reward_tendsto {ι : Type*} {l : Filter ι} {Y γ : ℝ} (R : RecoveryState Y)
    (hY : 0 < Y) (hγ : 0 ≤ γ) {h : ι → ℝ} {N : ι → ℕ}
    (hh : ∀ i, 0 < h i) (hNY : ∀ i, (N i : ℝ) * h i ≤ Y)
    (hzero : Tendsto h l (𝓝 0)) (hend : Tendsto (fun i ↦ (N i : ℝ) * h i) l (𝓝 Y)) :
    Tendsto (fun i ↦ h i * R.discreteReward γ (hh i) (N i) (hNY i)) l
      (𝓝 (∫ y in 0..Y, R.energy y ^ (-γ))) := by
  obtain ⟨C, _hC, hbound⟩ := R.exists_reward_error_bound hY hγ
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsmall : ∀ᶠ i in l, h i ≤ 1 := hzero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_
    (show Tendsto (fun i ↦ C * h i + (Y - (N i : ℝ) * h i)) l (𝓝 0) by
      convert (hzero.const_mul C).add (tendsto_const_nhds.sub hend) using 1; simp)
  filter_upwards [hsmall] with i hi
  simpa only [Real.norm_eq_abs] using hbound (h i) (hh i) hi (N i) (hNY i)

end RecoveryState
end
end krylov.Asymptotics

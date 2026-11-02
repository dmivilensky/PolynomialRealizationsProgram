import krylov.Asymptotics.RecoveryEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: main_krylov, lower bound in thm:limit.
Use: genuine right Riemann sums and the actual sampled Christoffel energies
converge to the continuum type reward. Positivity controls the negative
powers uniformly, including arbitrary positive exponents.
Source: interval integration, the mean value inequality, and the proved
first-order recovery energy estimate.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory Finset
open scoped BigOperators

/-- A right rectangle has a genuine quadratic local error under a
Lipschitz bound on its integrand. -/
theorem right_rectangle_error {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hL : 0 ≤ L)
    (hLip : ∀ x ∈ Icc a b, |f b - f x| ≤ L * |b - x|) :
    |(b - a) * f b - ∫ x in a..b, f x| ≤ L * (b - a) ^ 2 := by
  have hi : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le hab]
  have hi' : IntervalIntegrable (fun _ : ℝ ↦ f b) volume a b := intervalIntegrable_const
  have heq : (b - a) * f b - ∫ x in a..b, f x = ∫ x in a..b, (f b - f x) := by
    rw [intervalIntegral.integral_sub hi' hi, intervalIntegral.integral_const, smul_eq_mul]
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (C := L * (b - a)) (f := fun x ↦ f b - f x) (fun x hx ↦ ?_)
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), pow_two, mul_assoc] using hb
  · rw [uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs]
    apply (hLip x ⟨hx.1.le, hx.2⟩).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
    exact mul_le_mul_of_nonneg_left (by linarith [hx.1]) hL

/-- A genuine finite right Riemann sum has uniform first-order error. -/
theorem right_riemann_error {f : ℝ → ℝ} {Y h L : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hNY : (N : ℝ) * h ≤ Y) (hL : 0 ≤ L)
    (hc : ContinuousOn f (Icc 0 Y))
    (hLip : ∀ x ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y, |f x - f z| ≤ L * |x - z|) :
    |h * ∑ k ∈ range N, f (((k : ℝ) + 1) * h) - ∫ x in 0..(N : ℝ) * h, f x| ≤ L * Y * h := by
  have hrec (j : ℕ) (hj : j < N) :
      |h * ∑ k ∈ range (j + 1), f (((k : ℝ) + 1) * h) - ∫ x in 0..((j + 1 : ℕ) : ℝ) * h, f x| ≤
        (1 + 0 * h) * |h * ∑ k ∈ range j, f (((k : ℝ) + 1) * h) - ∫ x in 0..(j : ℝ) * h, f x| + L * h ^ 2 := by
    let a := (j : ℝ) * h
    let b := ((j : ℝ) + 1) * h
    have ha : a ∈ Icc 0 Y := grid_mem hh hNY hj.le
    have hb : b ∈ Icc 0 Y := by simpa only [b, Nat.cast_succ] using grid_mem hh hNY (Nat.succ_le_of_lt hj)
    have hab : a ≤ b := by dsimp [a, b]; nlinarith
    have hba : b - a = h := by dsimp [a, b]; ring
    have hsub : Icc a b ⊆ Icc 0 Y := fun x hx ↦ ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    have hrect := right_rectangle_error hab (hc.mono hsub) hL
      (fun x hx ↦ hLip b hb x (hsub hx))
    rw [hba] at hrect
    have h0 : IntervalIntegrable f volume 0 a := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ha.1]
      exact hc.mono (fun x hx ↦ ⟨hx.1, hx.2.trans ha.2⟩)
    have h1 : IntervalIntegrable f volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab]
      exact hc.mono hsub
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0 h1
    simp only [zero_mul, add_zero, one_mul, sum_range_succ, Nat.cast_add, Nat.cast_one]
    change |h * ((∑ k ∈ range j, f (((k : ℝ) + 1) * h)) + f b) - ∫ x in 0..b, f x| ≤ _
    rw [← hadd]
    calc
      _ = |(h * (∑ k ∈ range j, f (((k : ℝ) + 1) * h)) - ∫ x in 0..a, f x) +
          (h * f b - ∫ x in a..b, f x)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl hrect)
  have ht := finite_grid_gronwall hL (by norm_num : (0 : ℝ) ≤ 0) hh hNY
    (e := fun j ↦ |h * ∑ k ∈ range j, f (((k : ℝ) + 1) * h) - ∫ x in 0..(j : ℝ) * h, f x|)
    (by simp) (fun _ _ ↦ abs_nonneg _) hrec (j := N) le_rfl
  simpa only [zero_mul, exp_zero, mul_one] using ht

/-- Negative powers are uniformly Lipschitz on the true energy range
`[1,∞)`. In particular no discretization-dependent compact bound is needed. -/
theorem negative_power_lipschitz {a b γ : ℝ} (hγ : 0 ≤ γ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |a ^ (-γ) - b ^ (-γ)| ≤ γ * |a - b| := by
  have hd (x : ℝ) (hx : x ∈ Ici (1 : ℝ)) :
      HasDerivWithinAt (fun x : ℝ ↦ x ^ (-γ)) ((-γ) * x ^ (-γ - 1)) (Ici 1) x :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))).hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Ici (1 : ℝ)) : ‖(-γ) * x ^ (-γ - 1)‖ ≤ γ := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hγ,
      abs_of_nonneg (rpow_nonneg (le_trans zero_le_one hx) _)]
    exact (mul_le_mul_of_nonneg_left (rpow_le_one_of_one_le_of_nonpos hx (by linarith)) hγ).trans_eq (mul_one γ)
  have ht := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Ici (1 : ℝ)) hb ha
  simpa only [Real.norm_eq_abs] using ht

/-- The genuine finite recovery reward differs from its continuum type
integral by O(h), uniformly in all admitted finite grids. -/
theorem exists_recovery_reward_error_bound {v φ p K : ℝ → ℝ} {Y γ : ℝ}
    (hY : 0 < Y) (hγ : 0 ≤ γ) (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hcv : ContDiffOn ℝ 1 v (Icc 0 Y))
    (hcφ : ContDiffOn ℝ 1 φ (Icc 0 Y)) (hcp : ContDiffOn ℝ 1 p (Icc 0 Y))
    (hcK : ContDiffOn ℝ 1 K (Icc 0 Y)) (hKone : ∀ y ∈ Icc 0 Y, 1 ≤ K y)
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1) (hK₀ : K 0 = 1)
    (hφ : ∀ y ∈ Icc 0 Y, HasDerivWithinAt φ ((v y)⁻¹ * p y) (Icc 0 Y) y)
    (hp : ∀ y ∈ Icc 0 Y, HasDerivWithinAt p (v y * φ y) (Icc 0 Y) y)
    (hK : ∀ y ∈ Icc 0 Y, HasDerivWithinAt K (v y * φ y ^ 2) (Icc 0 Y) y) :
    ∃ C > (0 : ℝ), ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ N : ℕ, ∀ hNY : (N : ℝ) * h ≤ Y,
      let S := recoveryString v hh N hNY hv
      |h * ∑ j ∈ range N, S.K (j + 1) ^ (-γ) - ∫ y in 0..(N : ℝ) * h, K y ^ (-γ)| ≤ C * h := by
  obtain ⟨C, hC, henergy⟩ := exists_recovery_energy_error_bound hY hv hcv hcφ hcp hφ₀ hp₀ hK₀ hφ hp hK
  have hpow : ContDiffOn ℝ 1 (fun y ↦ K y ^ (-γ)) (Icc 0 Y) :=
    hcK.rpow_const_of_ne (fun y hy ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (hKone y hy)))
  obtain ⟨L, hL, _, hLip⟩ := compact_C1_scalar_bounds hpow
  refine ⟨Y * γ * C + L * Y + 1, by positivity, ?_⟩
  intro h hh hh₁ N hNY
  let S := recoveryString v hh N hNY hv
  have herr (j : ℕ) (hj : j < N) :
      |S.K (j + 1) ^ (-γ) - K (((j : ℝ) + 1) * h) ^ (-γ)| ≤ γ * C * h := by
    have hb := grid_mem hh.le hNY (Nat.succ_le_of_lt hj)
    have ht := negative_power_lipschitz hγ (S.state_bounds (j + 1) (Nat.succ_le_of_lt hj)).2.2.1 (hKone _ hb)
    have he := henergy h hh hh₁ N hNY (j + 1) (Nat.succ_le_of_lt hj)
    calc
      _ ≤ γ * |S.K (j + 1) - K (((j : ℝ) + 1) * h)| := by
        simpa only [Nat.cast_succ] using ht
      _ ≤ γ * (C * h) := mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using he) hγ
      _ = _ := by ring
  have hsum : |h * ∑ j ∈ range N, S.K (j + 1) ^ (-γ) -
      h * ∑ j ∈ range N, K (((j : ℝ) + 1) * h) ^ (-γ)| ≤ Y * γ * C * h := by
    rw [← mul_sub, ← sum_sub_distrib, abs_mul, abs_of_pos hh]
    calc
      _ ≤ h * ∑ j ∈ range N, |S.K (j + 1) ^ (-γ) - K (((j : ℝ) + 1) * h) ^ (-γ)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hh.le
      _ ≤ h * ∑ _j ∈ range N, γ * C * h := by gcongr with j hj; exact herr j (mem_range.mp hj)
      _ = ((N : ℝ) * h) * γ * C * h := by simp; ring
      _ ≤ Y * γ * C * h := by gcongr
  have hquad := right_riemann_error hh.le hNY hL hpow.continuousOn hLip
  change |h * ∑ j ∈ range N, S.K (j + 1) ^ (-γ) - _| ≤ _
  calc
    _ ≤ |h * ∑ j ∈ range N, S.K (j + 1) ^ (-γ) -
        h * ∑ j ∈ range N, K (((j : ℝ) + 1) * h) ^ (-γ)| +
        |h * ∑ j ∈ range N, K (((j : ℝ) + 1) * h) ^ (-γ) - ∫ y in 0..(N : ℝ) * h, K y ^ (-γ)| :=
      abs_sub_le _ _ _
    _ ≤ (Y * γ * C + L * Y + 1) * h := by nlinarith [hsum, hquad]

end
end krylov.Asymptotics

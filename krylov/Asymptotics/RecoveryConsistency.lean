import krylov.Asymptotics.RecoveryDefect

/-!
Article: main_krylov, lower bound in thm:limit.
Use: uniform first-order position/slope convergence of the actual sampled
recovery strings. Actual type-time state equations, coefficient regularity
and compact bounds imply the local quadratic defect; discrete Grönwall then
gives the genuine global error. No convergence hypothesis is assumed.
Source: the proved Taylor, split-step stability and discrete Grönwall bounds.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set

/-- The actual split sampling has a quadratic local defect on a genuine
smooth type-time reference state. Endpoint derivatives are one-sided. -/
theorem recovery_step_defect {v φ p : ℝ → ℝ} {Y h V M L D : ℝ} {N j : ℕ}
    (hh : 0 < h) (hNY : (N : ℝ) * h ≤ Y) (hj : j < N)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hvBound : ∀ y ∈ Icc 0 Y, |v y| ≤ V ∧ |(v y)⁻¹| ≤ V)
    (hstateBound : ∀ y ∈ Icc 0 Y, |φ y| ≤ M ∧ |p y| ≤ M)
    (hcoefLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |v y - v z| ≤ L * |y - z| ∧ |(v y)⁻¹ - (v z)⁻¹| ≤ L * |y - z|)
    (hφ : ∀ y ∈ Icc 0 Y, HasDerivWithinAt φ ((v y)⁻¹ * p y) (Icc 0 Y) y)
    (hp : ∀ y ∈ Icc 0 Y, HasDerivWithinAt p (v y * φ y) (Icc 0 Y) y)
    (hφLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |(v y)⁻¹ * p y - (v z)⁻¹ * p z| ≤ D * |y - z|)
    (hpLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |v y * φ y - v z * φ z| ≤ D * |y - z|) :
    ‖recoveryStep v h j (φ ((j : ℝ) * h), p ((j : ℝ) * h)) -
        (φ (((j : ℝ) + 1) * h), p (((j : ℝ) + 1) * h))‖ ≤
      ((L + V ^ 2) * M + D) * h ^ 2 := by
  let a := (j : ℝ) * h
  let b := ((j : ℝ) + 1) * h
  let m := ((j : ℝ) + 1 / 2) * h
  have ha : a ∈ Icc 0 Y := grid_mem hh.le hNY hj.le
  have hb : b ∈ Icc 0 Y := by
    simpa only [Nat.cast_succ] using grid_mem hh.le hNY (Nat.succ_le_of_lt hj)
  have hm : m ∈ Icc 0 Y := midpoint_grid_mem hh.le hNY hj
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have hba : b - a = h := by dsimp [a, b]; ring
  have hma : |m - a| ≤ h := by
    dsimp [m, a]
    rw [show ((j : ℝ) + 1 / 2) * h - (j : ℝ) * h = h / 2 by ring,
      abs_of_nonneg (by positivity)]
    linarith
  have hsub : Icc a b ⊆ Icc 0 Y := fun _ hy ↦ ⟨ha.1.trans hy.1, hy.2.trans hb.2⟩
  have hφTaylor := taylor_increment_bound_within hab hD
    (fun y hy ↦ (hφ y (hsub hy)).mono hsub)
    (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hφLip y (hsub hy) a ha)
  have hpTaylor := taylor_increment_bound_within hab hD
    (fun y hy ↦ (hp y (hsub hy)).mono hsub)
    (fun y hy ↦ by simpa only [Real.norm_eq_abs] using hpLip y (hsub hy) a ha)
  have hvarA : |(v m)⁻¹ - (v a)⁻¹| ≤ L * h :=
    ((hcoefLip m hm a ha).2).trans (mul_le_mul_of_nonneg_left hma hL)
  have hvarB : |v b - v a| ≤ L * h := by
    have ht := (hcoefLip b hb a ha).1
    rwa [hba, abs_of_pos hh] at ht
  apply driftImpulseStep_defect hh.le hV hM hL hD (inv_nonneg.mpr (hv m hm).le)
    (hv b hb).le ((le_abs_self _).trans (hvBound m hm).2)
    ((le_abs_self _).trans (hvBound b hb).1) (hstateBound a ha).1 (hstateBound a ha).2 hvarA hvarB
  · simpa only [hba, Real.norm_eq_abs, smul_eq_mul, mul_assoc] using hφTaylor
  · simpa only [hba, Real.norm_eq_abs, smul_eq_mul, mul_assoc] using hpTaylor

/-- The source's genuine uniform `O(h)` state error for the constructed
positive sampled string. The compact constants depend on the fixed continuum
window, not on the grid size or number of mass sites. -/
theorem recovery_state_error_bound {v φ p : ℝ → ℝ} {Y h V M L D : ℝ} {N : ℕ}
    (hh : 0 < h) (hh₁ : h ≤ 1) (hNY : (N : ℝ) * h ≤ Y)
    (hV : 0 ≤ V) (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hvBound : ∀ y ∈ Icc 0 Y, |v y| ≤ V ∧ |(v y)⁻¹| ≤ V)
    (hstateBound : ∀ y ∈ Icc 0 Y, |φ y| ≤ M ∧ |p y| ≤ M)
    (hcoefLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |v y - v z| ≤ L * |y - z| ∧ |(v y)⁻¹ - (v z)⁻¹| ≤ L * |y - z|)
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1)
    (hφ : ∀ y ∈ Icc 0 Y, HasDerivWithinAt φ ((v y)⁻¹ * p y) (Icc 0 Y) y)
    (hp : ∀ y ∈ Icc 0 Y, HasDerivWithinAt p (v y * φ y) (Icc 0 Y) y)
    (hφLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |(v y)⁻¹ * p y - (v z)⁻¹ * p z| ≤ D * |y - z|)
    (hpLip : ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y,
      |v y * φ y - v z * φ z| ≤ D * |y - z|)
    {j : ℕ} (hj : j ≤ N) :
    let S := recoveryString v hh N hNY hv
    ‖(S.φ j, S.p j) - (φ ((j : ℝ) * h), p ((j : ℝ) * h))‖ ≤
      ((L + V ^ 2) * M + D) * Y * exp ((V + V ^ 2) * Y) * h := by
  dsimp only
  rw [recoveryString_pair_evolution]
  apply evolution_error_bound (C := (L + V ^ 2) * M + D) (L := V + V ^ 2)
    (reference := fun j ↦ (φ ((j : ℝ) * h), p ((j : ℝ) * h)))
    (by positivity) (by positivity) hh.le hNY (by simp [hφ₀, hp₀]) ?_ ?_ hj
  · intro k hk z w
    have hmid := midpoint_grid_mem hh.le hNY hk
    have hend := grid_mem hh.le hNY (Nat.succ_le_of_lt hk)
    have hkb : (((k : ℝ) + 1) * h) ∈ Icc 0 Y := by simpa only [Nat.cast_succ] using hend
    exact driftImpulseStep_stable hh.le hh₁ (inv_nonneg.mpr (hv _ hmid).le) (hv _ hkb).le
      ((le_abs_self _).trans (hvBound _ hmid).2) ((le_abs_self _).trans (hvBound _ hkb).1) z w
  · intro k hk
    simpa only [Nat.cast_succ] using recovery_step_defect hh hNY hk hV hM hL hD hv hvBound
      hstateBound hcoefLip hφ hp hφLip hpLip

end
end krylov.Asymptotics

import nesterov.Flow.Constants

/-!
Article: Corollary `damping`.
Use: exact optimal damping, equality cases, and componentwise domination by
the Pareto arc; these are properties of the constants, independent of ODEs.
-/

noncomputable section

namespace nesterov.Flow

theorem cQ_le_sqrt {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) : cQ θ m ≤ Real.sqrt m := by
  have hs := Real.sq_sqrt hm.le
  have hsn := Real.sqrt_nonneg m
  rcases le_total (θ ^ 2) (4 * m) with h | h
  · rw [cQ_eq_half h]
    nlinarith
  · have hd := delta_cQ_eq_zero h
    have hc := cQ_pos hθ hm
    have hh := cQ_le_half θ m
    dsimp [delta] at hd
    nlinarith

theorem cQ_critical {m : ℝ} (hm : 0 ≤ m) : cQ (2 * Real.sqrt m) m = Real.sqrt m := by
  rw [cQ_eq_half (by nlinarith [Real.sq_sqrt hm])]
  ring

theorem cQ_eq_sqrt_iff {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    cQ θ m = Real.sqrt m ↔ θ = 2 * Real.sqrt m := by
  constructor
  · intro he
    rcases le_total (θ ^ 2) (4 * m) with h | h
    · rw [cQ_eq_half h] at he
      linarith
    · have hd := delta_cQ_eq_zero h
      rw [he] at hd
      have hs := Real.sq_sqrt hm.le
      have hsp := Real.sqrt_pos.mpr hm
      dsimp [delta] at hd
      nlinarith
  · rintro rfl
    exact cQ_critical hm.le

theorem critical_le_nonlinear_optimal {m : ℝ} (hm : 0 ≤ m) :
    2 * Real.sqrt m ≤ 3 * Real.sqrt (m / 2) := by
  have h1 := Real.sq_sqrt hm
  have h2 := Real.sq_sqrt (show 0 ≤ m / 2 by positivity)
  have hn1 := Real.sqrt_nonneg m
  have hn2 := Real.sqrt_nonneg (m / 2)
  nlinarith

theorem cQ_at_nonlinear_optimal {m : ℝ} (hm : 0 < m) :
    cQ (3 * Real.sqrt (m / 2)) m = Real.sqrt (m / 2) := by
  let a := Real.sqrt (m / 2)
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have hs : a ^ 2 = m / 2 := Real.sq_sqrt (by positivity)
  apply le_antisymm
  · by_contra h
    obtain ⟨_, hd⟩ := (lt_cQ_iff (3 * a) m a).mp (lt_of_not_ge h)
    dsimp [delta] at hd
    nlinarith
  · have hd := delta_cQ_eq_zero (θ := 3 * a) (m := m) (by nlinarith)
    have hp := cQ_pos (θ := 3 * a) (m := m) (by positivity) hm
    have hh := cQ_le_half (3 * a) m
    dsimp [delta] at hd
    nlinarith

theorem cF_at_nonlinear_optimal {m : ℝ} (hm : 0 < m) :
    cF (3 * Real.sqrt (m / 2)) m = Real.sqrt (m / 2) := by
  rw [cF, cQ_at_nonlinear_optimal hm]
  simp

theorem cQ_le_nonlinear_optimal_of_damping_ge {θ m : ℝ} (hm : 0 < m)
    (hθ : 3 * Real.sqrt (m / 2) ≤ θ) : cQ θ m ≤ Real.sqrt (m / 2) := by
  by_contra h
  obtain ⟨_, hd⟩ := (lt_cQ_iff θ m (Real.sqrt (m / 2))).mp (lt_of_not_ge h)
  have hs := Real.sq_sqrt (show 0 ≤ m / 2 by positivity)
  have ha := Real.sqrt_nonneg (m / 2)
  have hh := mul_le_mul_of_nonneg_right hθ ha
  dsimp [delta] at hd
  nlinarith

theorem cQ_lt_nonlinear_optimal_of_damping_gt {θ m : ℝ} (hm : 0 < m)
    (hθ : 3 * Real.sqrt (m / 2) < θ) : cQ θ m < Real.sqrt (m / 2) := by
  have hle := cQ_le_nonlinear_optimal_of_damping_ge hm hθ.le
  apply lt_of_le_of_ne hle
  intro he
  have hs := Real.sq_sqrt (show 0 ≤ m / 2 by positivity)
  have ha := Real.sqrt_pos.mpr (show 0 < m / 2 by positivity)
  have hθ0 : 0 < θ := by linarith
  have hd := delta_cQ_eq_zero (θ := θ) (m := m) (by nlinarith)
  rw [he] at hd
  have hh := mul_lt_mul_of_pos_right hθ ha
  dsimp [delta] at hd
  nlinarith

/-- Corollary damping: the full-class optimum is sqrt(m/2). -/
theorem cF_le_optimal {θ m : ℝ} (hm : 0 < m) : cF θ m ≤ Real.sqrt (m / 2) := by
  by_cases hθ : θ ≤ 3 * Real.sqrt (m / 2)
  · exact (cF_le_third θ m).trans (by linarith)
  · exact (cF_le_cQ θ m).trans (cQ_le_nonlinear_optimal_of_damping_ge hm (by linarith))

/-- Corollary damping: equality determines the damping uniquely. -/
theorem cF_eq_optimal_iff {θ m : ℝ} (hm : 0 < m) :
    cF θ m = Real.sqrt (m / 2) ↔ θ = 3 * Real.sqrt (m / 2) := by
  constructor
  · intro he
    have hle := cF_le_third θ m
    rw [he] at hle
    apply le_antisymm
    · by_contra h
      have hh := cQ_lt_nonlinear_optimal_of_damping_gt hm (lt_of_not_ge h)
      have hc := cF_le_cQ θ m
      rw [he] at hc
      linarith
    · linarith
  · rintro rfl
    exact cF_at_nonlinear_optimal hm

theorem cF_eq_third_of_damping_le_optimal {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hdamp : θ ≤ 3 * Real.sqrt (m / 2)) : cF θ m = θ / 3 := by
  apply min_eq_left
  by_contra h
  have hlt : cQ θ m < θ / 3 := lt_of_not_ge h
  have hs := Real.sq_sqrt (show 0 ≤ m / 2 by positivity)
  have hsn := Real.sqrt_nonneg (m / 2)
  rcases le_total (θ ^ 2) (4 * m) with h | h
  · rw [cQ_eq_half h] at hlt
    linarith
  · have hd := delta_cQ_eq_zero h
    have hc := cQ_pos hθ hm
    dsimp [delta] at hd
    have hp := mul_pos hc (show 0 < θ / 3 - cQ θ m by linarith)
    nlinarith

theorem cF_eq_cQ_of_damping_ge_optimal {θ m : ℝ} (hm : 0 < m)
    (hdamp : 3 * Real.sqrt (m / 2) ≤ θ) : cF θ m = cQ θ m := by
  apply min_eq_right
  exact (cQ_le_nonlinear_optimal_of_damping_ge hm hdamp).trans (by linarith)

/-- Corollary damping: every pair is dominated by a point of the stated arc. -/
theorem pareto_domination {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    ∃ θ' : ℝ, 2 * Real.sqrt m ≤ θ' ∧ θ' ≤ 3 * Real.sqrt (m / 2) ∧
      cQ θ m ≤ cQ θ' m ∧ cF θ m ≤ θ' / 3 ∧ cF θ' m = θ' / 3 := by
  by_cases hleft : θ ≤ 2 * Real.sqrt m
  · refine ⟨2 * Real.sqrt m, le_rfl, critical_le_nonlinear_optimal hm.le, ?_, ?_, ?_⟩
    · rw [cQ_critical hm.le]
      exact cQ_le_sqrt hθ hm
    · exact (cF_le_third θ m).trans (by linarith)
    · exact cF_eq_third_of_damping_le_optimal (by positivity) hm
        (critical_le_nonlinear_optimal hm.le)
  · by_cases hright : θ ≤ 3 * Real.sqrt (m / 2)
    · refine ⟨θ, by linarith, hright, le_rfl, cF_le_third θ m,
        cF_eq_third_of_damping_le_optimal hθ hm hright⟩
    · refine ⟨3 * Real.sqrt (m / 2), critical_le_nonlinear_optimal hm.le, le_rfl, ?_, ?_, ?_⟩
      · rw [cQ_at_nonlinear_optimal hm]
        exact cQ_le_nonlinear_optimal_of_damping_ge hm (by linarith)
      · have h := cF_le_optimal (θ := θ) hm
        linarith
      · rw [cF_at_nonlinear_optimal hm]
        ring

end nesterov.Flow

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Article: §3 and Lemma `cQprop` (Appendix B).
Use: the exact quadratic and nonlinear heavy-ball flow constants.  The
characterization by the open stability region also proves their scaling law.
-/

noncomputable section

namespace nesterov.Flow

/-- The shifted characteristic polynomial of the heavy-ball flow. -/
def delta (θ m c : ℝ) : ℝ := c ^ 2 - θ * c + m

/-- Slowest decay exponent of the scalar quadratic oscillator. -/
def cQ (θ m : ℝ) : ℝ :=
  if θ ^ 2 < 4 * m then θ / 2 else (θ - Real.sqrt (θ ^ 2 - 4 * m)) / 2

/-- The exact exponent on the full strongly convex class. -/
def cF (θ m : ℝ) : ℝ := min (θ / 3) (cQ θ m)

theorem cQ_le_half (θ m : ℝ) : cQ θ m ≤ θ / 2 := by
  unfold cQ
  split_ifs
  · exact le_rfl
  · linarith [Real.sqrt_nonneg (θ ^ 2 - 4 * m)]

/-- Appendix B, Lemma `cQprop`(a), including negative test exponents. -/
theorem lt_cQ_iff (θ m c : ℝ) :
    c < cQ θ m ↔ c < θ / 2 ∧ 0 < delta θ m c := by
  unfold cQ delta
  split_ifs with h
  · constructor
    · intro hc
      exact ⟨hc, by nlinarith [sq_nonneg (c - θ / 2)]⟩
    · exact And.left
  · have hs := Real.sqrt_nonneg (θ ^ 2 - 4 * m)
    have hsq := Real.sq_sqrt (show 0 ≤ θ ^ 2 - 4 * m by linarith)
    constructor
    · intro hc
      constructor
      · linarith
      · nlinarith [mul_pos (show 0 < θ - 2 * c - Real.sqrt (θ ^ 2 - 4 * m) by
          linarith) (show 0 < θ - 2 * c + Real.sqrt (θ ^ 2 - 4 * m) by linarith)]
    · rintro ⟨hc, hd⟩
      have hlt : Real.sqrt (θ ^ 2 - 4 * m) < θ - 2 * c := by
        nlinarith
      linarith

theorem cQ_pos {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) : 0 < cQ θ m := by
  exact (lt_cQ_iff θ m 0).mpr ⟨by linarith, by simpa [delta] using hm⟩

theorem cF_pos {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) : 0 < cF θ m :=
  lt_min (by linarith) (cQ_pos hθ hm)

theorem lt_cF_iff (θ m c : ℝ) :
    c < cF θ m ↔ c < θ / 3 ∧ c < θ / 2 ∧ 0 < delta θ m c := by
  rw [cF, lt_min_iff, lt_cQ_iff]

theorem delta_scale (α θ m c : ℝ) :
    delta (α * θ) (α ^ 2 * m) (α * c) = α ^ 2 * delta θ m c := by
  unfold delta
  ring

/-- Appendix B, Lemma `cQprop`(b): covariance of the exact quadratic rate. -/
theorem cQ_scale {α : ℝ} (hα : 0 < α) (θ m : ℝ) :
    cQ (α * θ) (α ^ 2 * m) = α * cQ θ m := by
  apply le_antisymm
  · by_contra h
    have ht : α * cQ θ m < cQ (α * θ) (α ^ 2 * m) := lt_of_not_ge h
    obtain ⟨hh, hd⟩ := (lt_cQ_iff _ _ _).mp ht
    rw [delta_scale] at hd
    have hhalf : cQ θ m < θ / 2 := by nlinarith
    have hdelta : 0 < delta θ m (cQ θ m) := (mul_pos_iff_of_pos_left
      (sq_pos_of_pos hα)).mp hd
    exact (lt_irrefl (cQ θ m)) ((lt_cQ_iff _ _ _).mpr ⟨hhalf, hdelta⟩)
  · by_contra h
    have ht : cQ (α * θ) (α ^ 2 * m) / α < cQ θ m := by
      apply (div_lt_iff₀ hα).mpr
      nlinarith [lt_of_not_ge h]
    obtain ⟨hh, hd⟩ := (lt_cQ_iff _ _ _).mp ht
    have he : α * (cQ (α * θ) (α ^ 2 * m) / α) =
        cQ (α * θ) (α ^ 2 * m) := by field_simp
    have hhalf : cQ (α * θ) (α ^ 2 * m) < α * θ / 2 := by
      rw [← he]
      nlinarith
    have hdelta : 0 < delta (α * θ) (α ^ 2 * m) (cQ (α * θ) (α ^ 2 * m)) := by
      rw [← he, delta_scale]
      exact mul_pos (sq_pos_of_pos hα) hd
    exact (lt_irrefl (cQ (α * θ) (α ^ 2 * m)))
      ((lt_cQ_iff _ _ _).mpr ⟨hhalf, hdelta⟩)

/-- Appendix B, Lemma `cQprop`(b): covariance of the full-class rate. -/
theorem cF_scale {α : ℝ} (hα : 0 < α) (θ m : ℝ) :
    cF (α * θ) (α ^ 2 * m) = α * cF θ m := by
  rw [cF, cQ_scale hα, cF, mul_min_of_nonneg _ _ hα.le]
  congr 1
  ring

theorem cQ_eq_half {θ m : ℝ} (h : θ ^ 2 ≤ 4 * m) : cQ θ m = θ / 2 := by
  unfold cQ
  split_ifs with hh
  · rfl
  · have he : θ ^ 2 - 4 * m = 0 := by linarith
    simp [he]

theorem delta_cQ_eq_zero {θ m : ℝ} (h : 4 * m ≤ θ ^ 2) :
    delta θ m (cQ θ m) = 0 := by
  rw [cQ, ite_eq_right (by linarith)]
  have hs := Real.sq_sqrt (show 0 ≤ θ ^ 2 - 4 * m by linarith)
  dsimp [delta]
  nlinarith

theorem cF_le_third (θ m : ℝ) : cF θ m ≤ θ / 3 := min_le_left _ _

theorem cF_le_cQ (θ m : ℝ) : cF θ m ≤ cQ θ m := min_le_right _ _

end nesterov.Flow

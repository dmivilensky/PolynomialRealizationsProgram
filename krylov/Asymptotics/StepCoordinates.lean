import krylov.Asymptotics.Apriori
import krylov.Strings.FeedbackAlgebra

/-!
Article: main_krylov, apC:lem:step.
Use: the exact positive log increments and ratio geometry of an actual
finite drift/impulse string. All coordinates are computed from its masses
and gaps; no step identities are fields of an assumed certificate.
Source: the discrete Stieltjes recurrence and elementary logarithm algebra.
-/

/-!
Article: krylov, Lemma D.21 [apC:lem:step].

The genuine drift/impulse integrals give q≤k, the exact log increment, potential-loss estimate
and both full logarithmic-average product bounds.
Eplus and Eminus are continuously extended at zero; the article A^I is the reciprocal of the
Lean impulseAverage, so A^D/A^I becomes the displayed product.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Set
open krylov.Strings
open scoped BigOperators

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- Actual logarithmic position increment across one gap. -/
def driftLog (j : ℕ) : ℝ := log (S.φ (j + 1) / S.φ j)
/-- Actual logarithmic slope increment across the next mass. -/
def slopeLog (j : ℕ) : ℝ := log (S.p (j + 1) / S.p j)
/-- Actual logarithmic energy increment across the next mass. -/
def energyLog (j : ℕ) : ℝ := log (S.K (j + 1) / S.K j)
/-- Actual ratio along the free drift, in physical gap distance. -/
def driftRatio (j : ℕ) (u : ℝ) : ℝ := (S.φ j + u * S.p j) * S.p j / S.K j
/-- Actual ratio along the next impulse, unfolded by inserted mass. -/
def impulseRatio (j : ℕ) (u : ℝ) : ℝ :=
  S.φ (j + 1) * (S.p j + u * S.φ (j + 1)) /
    (S.K j + u * S.φ (j + 1) ^ 2)

/-- All three actual coordinates strictly increase across a positive edge. -/
theorem coordinates_strict {j : ℕ} (hj : j < N) :
    S.φ j < S.φ (j + 1) ∧ S.p j < S.p (j + 1) ∧ S.K j < S.K (j + 1) := by
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  have hφ' := (S.state_bounds (j + 1) (by omega)).1
  have hgap := S.gap_pos j hj
  have hmass := S.mass_pos (j + 1) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [S.φ_succ]
    exact lt_add_of_pos_right _ (mul_pos hgap (by linarith))
  · rw [S.p_succ]
    exact lt_add_of_pos_right _ (mul_pos hmass (by linarith))
  · rw [S.K_succ]
    exact lt_add_of_pos_right _ (mul_pos hmass (sq_pos_of_pos (by linarith)))

/-- The source increments are positive, and the energy log dominates the
slope log because the genuine pre-impulse state remains in the Bellman domain. -/
theorem log_bounds {j : ℕ} (hj : j < N) :
    0 < driftLog S j ∧ 0 < slopeLog S j ∧ slopeLog S j ≤ energyLog S j := by
  obtain ⟨hφ, hp, hK, hdom⟩ := S.state_bounds j hj.le
  obtain ⟨hφ', hp', hK', _⟩ := S.state_bounds (j + 1) (by omega)
  have hstrict := coordinates_strict S hj
  have hm := S.mass_pos (j + 1) (by omega)
  have hφp : S.K j ≤ S.φ (j + 1) * S.p j := by
    nlinarith [mul_nonneg (show 0 ≤ S.p j by linarith) (sub_nonneg.mpr hstrict.1.le)]
  have hrat : S.p (j + 1) / S.p j ≤ S.K (j + 1) / S.K j := by
    apply (div_le_div_iff₀ (by linarith : 0 < S.p j) (by linarith : 0 < S.K j)).2
    rw [S.p_succ, S.K_succ]
    nlinarith [mul_nonneg (mul_nonneg hm.le (show 0 ≤ S.φ (j + 1) by linarith))
      (sub_nonneg.mpr hφp)]
  exact ⟨log_pos ((one_lt_div (by linarith : 0 < S.φ j)).2 hstrict.1),
    log_pos ((one_lt_div (by linarith : 0 < S.p j)).2 hstrict.2.1),
    log_le_log (div_pos (by linarith) (by linarith)) hrat⟩

/-- The ratio log is exactly the position log plus slope log minus energy log. -/
theorem ratio_log_increment {j : ℕ} (hj : j < N) :
    log (S.ratio (j + 1)) - log (S.ratio j) =
      driftLog S j + slopeLog S j - energyLog S j := by
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  obtain ⟨hφ', hp', hK', _⟩ := S.state_bounds (j + 1) (by omega)
  have hnφ : S.φ j ≠ 0 := by linarith
  have hnp : S.p j ≠ 0 := by linarith
  have hnK : S.K j ≠ 0 := by linarith
  have hnφ' : S.φ (j + 1) ≠ 0 := by linarith
  have hnp' : S.p (j + 1) ≠ 0 := by linarith
  have hnK' : S.K (j + 1) ≠ 0 := by linarith
  simp only [krylov.Strings.DiscreteString.ratio, driftLog, slopeLog, energyLog,
    log_div (mul_ne_zero hnφ' hnp') hnK', log_div (mul_ne_zero hnφ hnp) hnK,
    log_mul hnφ' hnp', log_mul hnφ hnp, log_div hnφ' hnφ, log_div hnp' hnp,
    log_div hnK' hnK]
  ring

/-- The free-drift ratio stays between its actual endpoint ratios. -/
theorem driftRatio_bounds {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    S.ratio j ≤ driftRatio S j u ∧
      driftRatio S j u ≤ S.φ (j + 1) * S.p j / S.K j := by
  obtain ⟨_, hp, hK, _⟩ := S.state_bounds j hj.le
  have hpp : 0 ≤ S.p j := by linarith
  have hKp : 0 ≤ S.K j := by linarith
  dsimp [driftRatio, krylov.Strings.DiscreteString.ratio]
  constructor
  · exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hu.1 (sq_nonneg (S.p j))]) hKp
  · rw [S.φ_succ]
    exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sq_nonneg (S.p j))]) hKp

/-- Monotonicity of a genuine impulse ratio follows directly by multiplying
positive denominators; it needs no differentiability of the finite string. -/
theorem impulseRatio_antitone {j : ℕ} (hj : j < N) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) : impulseRatio S j v ≤ impulseRatio S j u := by
  obtain ⟨_, hp, hK, hdom⟩ := S.state_bounds j hj.le
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hφp : S.K j ≤ S.φ (j + 1) * S.p j := by
    have hstrict := (coordinates_strict S hj).1
    nlinarith [mul_nonneg (show 0 ≤ S.p j by linarith) (sub_nonneg.mpr hstrict.le)]
  have hdu : 0 < S.K j + u * S.φ (j + 1) ^ 2 := by positivity
  have hdv : 0 < S.K j + v * S.φ (j + 1) ^ 2 := by
    have hv : 0 ≤ v := hu.trans huv
    positivity
  dsimp [impulseRatio]
  apply (div_le_div_iff₀ hdv hdu).2
  have hnonneg := mul_nonneg (sub_nonneg.mpr huv)
    (mul_nonneg (sq_nonneg (S.φ (j + 1))) (sub_nonneg.mpr hφp))
  nlinarith only [hnonneg]

/-- Exact endpoint and monotonicity bounds on the unfolded mass impulse. -/
theorem impulseRatio_bounds {j : ℕ} (hj : j < N) {u : ℝ}
    (hu : u ∈ Icc 0 (S.mass (j + 1))) :
    S.ratio (j + 1) ≤ impulseRatio S j u ∧
      impulseRatio S j u ≤ S.φ (j + 1) * S.p j / S.K j := by
  have hleft := impulseRatio_antitone S hj hu.1 hu.2
  have hright := impulseRatio_antitone S hj (u := 0) (by norm_num) hu.1
  simpa only [impulseRatio, krylov.Strings.DiscreteString.ratio, ← S.p_succ, ← S.K_succ,
    zero_mul, add_zero] using And.intro hleft hright

end DiscreteString
end
end krylov.Asymptotics

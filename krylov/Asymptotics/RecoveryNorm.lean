import krylov.Asymptotics.RecoveryString
import krylov.Strings.DiscreteGershgorin
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Article: main_krylov, thm:limit, lower recovery spectral control.
Use: the genuine sampled string has spectral radius at most
`4 exp(L h) / h²`, hence the sharp leading `4/h²`. The distinguished
initial unit mass only improves the row bounds when `h v(0) ≤ 1`.
Source: the literal physical Gershgorin rows and local log-density control.
-/

namespace krylov.Asymptotics
noncomputable section
open Set Real krylov.Strings
open scoped Matrix.Norms.L2Operator

private theorem density_ratio {v : ℝ → ℝ} {Y L h x y : ℝ}
    (hL : 0 ≤ L) (hv : ∀ z ∈ Icc 0 Y, 0 < v z)
    (hlog : ∀ a ∈ Icc 0 Y, ∀ b ∈ Icc 0 Y,
      |log (v a) - log (v b)| ≤ L * |a - b|)
    (hx : x ∈ Icc 0 Y) (hy : y ∈ Icc 0 Y) (hxy : |x - y| ≤ h) :
    v x ≤ exp (L * h) * v y := by
  have he := exp_le_exp.mpr ((le_abs_self _).trans
    ((hlog x hx y hy).trans (mul_le_mul_of_nonneg_left hxy hL)))
  rw [exp_sub, exp_log (hv x hx), exp_log (hv y hy)] at he
  exact (div_le_iff₀ (hv y hy)).mp he

/-- Every actual sampled mass dominates the regular density quadrature
mass, including the distinguished atom at the origin. -/
theorem recovery_mass_ge_sample {v : ℝ → ℝ} {Y h : ℝ} (hh : 0 < h)
    (N : ℕ) (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hzero : h * v 0 ≤ 1) (j : ℕ) :
    h * v ((j : ℝ) * h) ≤ (recoveryString v hh N hNY hv).mass j := by
  by_cases hj : j = 0
  · simpa [recoveryString, hj] using hzero
  · simp [recoveryString, hj]

/-- Each incident diagonal edge term has the same sharp mesh-scale bound.
The two endpoint rows obey the same estimate as the interior rows. -/
theorem recovery_edge_diagonal_le {v : ℝ → ℝ} {Y h L : ℝ} (hh : 0 < h)
    (N : ℕ) (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hL : 0 ≤ L) (hzero : h * v 0 ≤ 1)
    (hlog : ∀ a ∈ Icc 0 Y, ∀ b ∈ Icc 0 Y,
      |log (v a) - log (v b)| ≤ L * |a - b|)
    (k j : ℕ) (hk : k < N) (hj : j = k ∨ j = k + 1) :
    let S := recoveryString v hh N hNY hv
    (S.gap k)⁻¹ * (S.mass j)⁻¹ ≤ exp (L * h) / h ^ 2 := by
  dsimp only
  let S := recoveryString v hh N hNY hv
  have hjN : j ≤ N := by omega
  have hx := midpoint_grid_mem hh.le hNY hk
  have hy := grid_mem hh.le hNY hjN
  have hd : |((k : ℝ) + 1 / 2) * h - (j : ℝ) * h| ≤ h := by
    rcases hj with hj | hj
    · rw [hj, abs_of_nonneg (by nlinarith : 0 ≤ ((k : ℝ) + 1 / 2) * h - (k : ℝ) * h)]
      linarith
    · rw [hj]
      push_cast
      rw [abs_of_nonpos (by nlinarith : ((k : ℝ) + 1 / 2) * h - ((k : ℝ) + 1) * h ≤ 0)]
      linarith
  have hr := density_ratio hL hv hlog hx hy hd
  have hm := recovery_mass_ge_sample hh N hNY hv hzero j
  have hmp := S.mass_pos j hjN
  change (h / v (((k : ℝ) + 1 / 2) * h))⁻¹ * (S.mass j)⁻¹ ≤ _
  rw [inv_div, ← div_eq_mul_inv]
  apply (div_le_iff₀ hmp).2
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hh (sq_pos_of_pos hh)).2
  have he := mul_le_mul_of_nonneg_left hm (exp_pos (L * h)).le
  nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg h)]

/-- The true off-diagonal edge term obeys the same bound as its two
diagonal terms, by the arithmetic--geometric mean inequality. -/
theorem recovery_edge_offDiagonal_le {v : ℝ → ℝ} {Y h L : ℝ} (hh : 0 < h)
    (N : ℕ) (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hL : 0 ≤ L) (hzero : h * v 0 ≤ 1)
    (hlog : ∀ a ∈ Icc 0 Y, ∀ b ∈ Icc 0 Y,
      |log (v a) - log (v b)| ≤ L * |a - b|) (k : ℕ) (hk : k < N) :
    let S := recoveryString v hh N hNY hv
    (S.gap k)⁻¹ * (sqrt (S.mass k))⁻¹ * (sqrt (S.mass (k + 1)))⁻¹ ≤
      exp (L * h) / h ^ 2 := by
  dsimp only
  let S := recoveryString v hh N hNY hv
  have h₀ := recovery_edge_diagonal_le hh N hNY hv hL hzero hlog k k hk (Or.inl rfl)
  have h₁ := recovery_edge_diagonal_le hh N hNY hv hL hzero hlog k (k + 1) hk (Or.inr rfl)
  have hs₀ : ((sqrt (S.mass k))⁻¹) ^ 2 = (S.mass k)⁻¹ := by
    rw [inv_pow, sq_sqrt (S.mass_pos k (by omega)).le]
  have hs₁ : ((sqrt (S.mass (k + 1)))⁻¹) ^ 2 = (S.mass (k + 1))⁻¹ := by
    rw [inv_pow, sq_sqrt (S.mass_pos (k + 1) (by omega)).le]
  have ha : 0 ≤ (S.gap k)⁻¹ := inv_nonneg.mpr (S.gap_pos k hk).le
  have ham := mul_nonneg ha (sq_nonneg ((sqrt (S.mass k))⁻¹ - (sqrt (S.mass (k + 1)))⁻¹))
  change (S.gap k)⁻¹ * (S.mass k)⁻¹ ≤ _ at h₀
  change (S.gap k)⁻¹ * (S.mass (k + 1))⁻¹ ≤ _ at h₁
  nlinarith [hs₀, hs₁]

/-- Uniform spectral control of the genuine recovery strings. The bound
has the sharp leading coefficient four as the mesh tends to zero. -/
theorem recovery_spectralRadius_le {v : ℝ → ℝ} {Y h L : ℝ} (hh : 0 < h)
    (N : ℕ) (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hL : 0 ≤ L) (hzero : h * v 0 ≤ 1)
    (hlog : ∀ a ∈ Icc 0 Y, ∀ b ∈ Icc 0 Y,
      |log (v a) - log (v b)| ≤ L * |a - b|) :
    (recoveryString v hh N hNY hv).spectralRadius ≤ 4 * exp (L * h) / h ^ 2 := by
  let S := recoveryString v hh N hNY hv
  let C := exp (L * h) / h ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply S.spectralRadius_le_of_gershgorinRows (by positivity)
  intro i
  have hd₀ : (if i.val < N then (S.gap i.val)⁻¹ * (S.mass i.val)⁻¹ else 0) ≤ C := by
    split_ifs with hi
    · exact recovery_edge_diagonal_le hh N hNY hv hL hzero hlog _ _ hi (Or.inl rfl)
    · exact hC
  have hd₁ : (if 0 < i.val then (S.gap (i.val - 1))⁻¹ * (S.mass i.val)⁻¹ else 0) ≤ C := by
    split_ifs with hi
    · exact recovery_edge_diagonal_le hh N hNY hv hL hzero hlog _ _ (by omega) (Or.inr (by omega))
    · exact hC
  have ho₀ : (if i.val < N then (S.gap i.val)⁻¹ *
      (sqrt (S.mass i.val))⁻¹ * (sqrt (S.mass (i.val + 1)))⁻¹ else 0) ≤ C := by
    split_ifs with hi
    · exact recovery_edge_offDiagonal_le hh N hNY hv hL hzero hlog _ hi
    · exact hC
  have ho₁ : (if 0 < i.val then (S.gap (i.val - 1))⁻¹ *
      (sqrt (S.mass (i.val - 1)))⁻¹ * (sqrt (S.mass i.val))⁻¹ else 0) ≤ C := by
    split_ifs with hi
    · have he : i.val - 1 + 1 = i.val := by omega
      simpa only [he] using recovery_edge_offDiagonal_le hh N hNY hv hL hzero hlog
        (i.val - 1) (by omega)
    · exact hC
  have hr : (if i.val = N then S.robin * (S.mass i.val)⁻¹ else 0) = 0 := by
    simp only [S, recoveryString, zero_mul, ite_self]
  change S.gershgorinRow i ≤ _
  unfold DiscreteString.gershgorinRow DiscreteString.offDiagonalRow
  rw [hr]
  dsimp only [C] at hd₀ hd₁ ho₀ ho₁
  rw [mul_div_assoc]
  linarith

end
end krylov.Asymptotics

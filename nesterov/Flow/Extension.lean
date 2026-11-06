import nesterov.Flow.Model
import polyak.Interpolation.Extension

/-!
Article: Appendix B, Lemma `extend`.
Use: strict support margins and Lipschitz orbit gradients produce one global
smooth strongly convex objective.  The arbitrary-set construction is reused
from Polyak's proved conjugate interpolation theorem.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Arbitrary convex M-smooth interpolation, obtained by scaling Polyak's
global convex 2-smooth extension.  This keeps the exact constant 1/(2M). -/
theorem exists_convex_smooth_interpolant {x G : I → E} {F : I → ℝ} {M : ℝ}
    (hM : 0 < M)
    (h : ∀ i j, F j + ⟪G j, x i - x j⟫_ℝ + ‖G i - G j‖ ^ 2 / (2 * M) ≤ F i)
    (star : I) (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ f : E → ℝ, Differentiable ℝ f ∧
      (∀ u v, f u + ⟪gradient f u, v - u⟫_ℝ ≤ f v) ∧
      (∀ u v, ‖gradient f u - gradient f v‖ ≤ M * ‖u - v‖) ∧
      (∀ i, f (x i) = F i ∧ gradient f (x i) = G i) := by
  let a : ℝ := 2 / M
  have ha : 0 < a := by dsimp [a]; positivity
  have haM : a * M = 2 := by dsimp [a]; field_simp
  have ht : polyak.Interpolation.ConvexTableFeasible x (fun i => a • G i) (fun i => a * F i) := by
    intro i j
    have hh := mul_le_mul_of_nonneg_left (h i j) ha.le
    simp only [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
      mul_pow, inner_smul_left, starRingEnd_apply, star_trivial]
    dsimp [a] at hh ⊢
    field_simp [ne_of_gt hM] at hh ⊢
    nlinarith
  obtain ⟨f, g, hg, hlower, _, hco, hdata⟩ :=
    polyak.Interpolation.exists_convex_interpolant ht star hx
      (by simp [hG]) (by simp [hF])
  let φ : E → ℝ := fun u => (a⁻¹) * f u
  have hgrad (u : E) : HasGradientAt φ (a⁻¹ • g u) u := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hg u).hasFDerivAt.const_mul (a⁻¹) using 1
    ext w
    simp [InnerProductSpace.toDual_apply_apply]
  have hglip (u v : E) : ‖g u - g v‖ ≤ 2 * ‖u - v‖ := by
    have hh := hco u v
    have hi := real_inner_le_norm (g u - g v) (u - v)
    have hn := norm_nonneg (g u - g v)
    by_contra hh'
    have hp : 0 < ‖g u - g v‖ := by linarith [norm_nonneg (u - v)]
    have hm := mul_pos hp (show 0 < ‖g u - g v‖ - 2 * ‖u - v‖ by linarith)
    nlinarith
  refine ⟨φ, fun u => (hgrad u).differentiableAt, ?_, ?_, ?_⟩
  · intro u v
    rw [(hgrad u).gradient]
    dsimp [φ]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    exact (by nlinarith [mul_le_mul_of_nonneg_left (hlower u v) (inv_pos.mpr ha).le])
  · intro u v
    rw [(hgrad u).gradient, (hgrad v).gradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹ * (2 * ‖u - v‖) := mul_le_mul_of_nonneg_left (hglip u v) (inv_pos.mpr ha).le
      _ = M * ‖u - v‖ := by dsimp [a]; field_simp
  · intro i
    obtain ⟨hval, hgi⟩ := hdata i
    constructor
    · dsimp [φ]
      rw [hval]
      field_simp
    · rw [(hgrad (x i)).gradient, hgi, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]

/-- Lemma `extend`, for a positive Lipschitz constant.  The conclusion is an
actual globally differentiable F_{m,L} objective with the prescribed gradient
and values on every index, including an infinite time continuum. -/
theorem extend_strict_support_pos {x G : I → E} {F : I → ℝ} {ε K m L : ℝ}
    (hε : 0 < ε) (hK : 0 < K) (hm : 0 < m) (hL : m < L)
    (hbound : m + K ^ 2 / (2 * ε) ≤ L)
    (hmargin : ∀ i j, ε * ‖x i - x j‖ ^ 2 ≤ F i - F j - ⟪G j, x i - x j⟫_ℝ)
    (hlip : ∀ i j, ‖G i - G j‖ ≤ K * ‖x i - x j‖)
    (star : I) (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ f : E → ℝ, polyak.CenteredSmoothStronglyConvex m L f ∧
      ∀ i, f (x i) = F i + m / 2 * ‖x i‖ ^ 2 ∧
        gradient f (x i) = m • x i + G i := by
  let M := K ^ 2 / (2 * ε)
  have hM : 0 < M := by dsimp [M]; positivity
  have htable : ∀ i j, F j + ⟪G j, x i - x j⟫_ℝ + ‖G i - G j‖ ^ 2 / (2 * M) ≤ F i := by
    intro i j
    have hs : ‖G i - G j‖ ^ 2 ≤ K ^ 2 * ‖x i - x j‖ ^ 2 := by
      have h := (sq_le_sq₀ (norm_nonneg (G i - G j))
        (mul_nonneg hK.le (norm_nonneg (x i - x j)))).mpr (hlip i j)
      simpa only [mul_pow] using h
    have he : (2 * M) * ε = K ^ 2 := by dsimp [M]; field_simp
    have hh : ‖G i - G j‖ ^ 2 / (2 * M) ≤ ε * ‖x i - x j‖ ^ 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
      nlinarith
    linarith [hmargin i j]
  obtain ⟨φ, hφ, hφlower, hφlip, hdata⟩ :=
    exists_convex_smooth_interpolant hM htable star hx hG hF
  let f : E → ℝ := fun u => m / 2 * ‖u‖ ^ 2 + φ u
  have hgrad (u : E) : HasGradientAt f (m • u + gradient φ u) u := by
    simpa only [one_mul, one_smul] using
      polyak.hasGradientAt_quadratic_add (hφ u).hasGradientAt m 1
  have hdata' (i : I) : f (x i) = F i + m / 2 * ‖x i‖ ^ 2 ∧
      gradient f (x i) = m • x i + G i := by
    constructor
    · dsimp [f]
      rw [(hdata i).1]
      ring
    · rw [(hgrad (x i)).gradient, (hdata i).2]
  refine ⟨f, ⟨⟨hm, hL, fun u => (hgrad u).differentiableAt, ?_, ?_⟩, ?_, ?_⟩, hdata'⟩
  · intro u v
    rw [(hgrad u).gradient]
    have hh := hφlower u v
    simp only [inner_sub_right] at hh
    dsimp [f]
    simp only [inner_add_left, inner_smul_left, inner_sub_right, norm_sub_sq_real,
      real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
    have hi : ⟪v, u⟫_ℝ = ⟪u, v⟫_ℝ := real_inner_comm u v
    rw [hi]
    nlinarith
  · intro u v
    rw [(hgrad u).gradient, (hgrad v).gradient]
    have he : m • u + gradient φ u - (m • v + gradient φ v) =
        m • (u - v) + (gradient φ u - gradient φ v) := by module
    rw [he]
    calc
      _ ≤ ‖m • (u - v)‖ + ‖gradient φ u - gradient φ v‖ := norm_add_le _ _
      _ ≤ m * ‖u - v‖ + M * ‖u - v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hm]
        linarith [hφlip u v]
      _ ≤ L * ‖u - v‖ := by nlinarith [norm_nonneg (u - v)]
  · have h := (hdata' star).1
    simpa [hx, hF] using h
  · have h := (hdata' star).2
    simpa [hx, hG] using h

/-- The scalar quadratic belongs to every nondegenerate smoothness class
above m, on every real Hilbert space. -/
theorem quadratic_gradient (m : ℝ) (u : E) :
    gradient (fun u : E => m / 2 * ‖u‖ ^ 2) u = m • u := by
  have hh := polyak.hasGradientAt_quadratic_add (hasGradientAt_const u (0 : ℝ)) m 0
  simpa only [mul_zero, add_zero, smul_zero] using hh.gradient

theorem quadratic_objective {m L : ℝ} (hm : 0 < m) (hL : m < L) :
    polyak.CenteredSmoothStronglyConvex m L (fun u : E => m / 2 * ‖u‖ ^ 2) := by
  have hgrad (u : E) : HasGradientAt (fun u : E => m / 2 * ‖u‖ ^ 2) (m • u) u := by
    simpa only [mul_zero, add_zero, smul_zero] using
      polyak.hasGradientAt_quadratic_add (hasGradientAt_const u (0 : ℝ)) m 0
  refine ⟨⟨hm, hL, fun u => (hgrad u).differentiableAt, ?_, ?_⟩, by simp, ?_⟩
  · intro u v
    rw [(hgrad u).gradient]
    simp only [inner_smul_left, inner_sub_right, norm_sub_sq_real,
      real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial]
    have hi : ⟪v, u⟫_ℝ = ⟪u, v⟫_ℝ := real_inner_comm u v
    rw [hi]
    linarith
  · intro u v
    rw [(hgrad u).gradient, (hgrad v).gradient, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hm]
    exact mul_le_mul_of_nonneg_right hL.le (norm_nonneg _)
  · rw [(hgrad 0).gradient, smul_zero]

/-- Lemma `extend` in full, including the degenerate zero-Lipschitz table.
All indices are retained in one global extension with the article's bound. -/
theorem extend_strict_support {x G : I → E} {F : I → ℝ} {ε K m L : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K) (hm : 0 < m) (hL : m < L)
    (hbound : m + K ^ 2 / (2 * ε) ≤ L)
    (hmargin : ∀ i j, ε * ‖x i - x j‖ ^ 2 ≤ F i - F j - ⟪G j, x i - x j⟫_ℝ)
    (hlip : ∀ i j, ‖G i - G j‖ ≤ K * ‖x i - x j‖)
    (star : I) (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ f : E → ℝ, polyak.CenteredSmoothStronglyConvex m L f ∧
      ∀ i, f (x i) = F i + m / 2 * ‖x i‖ ^ 2 ∧
        gradient f (x i) = m • x i + G i := by
  rcases hK.eq_or_lt with hK0 | hKpos
  · have hK' : K = 0 := hK0.symm
    have hgzero (i : I) : G i = 0 := by
      have h := hlip i star
      simp only [hK', hG, sub_zero, zero_mul] at h
      exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    have hxzero (i : I) : x i = 0 := by
      have h1 := hmargin i star
      have h2 := hmargin star i
      simp only [hx, hG, hF, hgzero, sub_zero, zero_sub, inner_zero_left,
        norm_neg] at h1 h2
      have hn : ‖x i‖ = 0 := by
        by_contra hn
        have hp := mul_pos hε (sq_pos_of_pos ((norm_nonneg (x i)).lt_of_ne' hn))
        linarith
      exact norm_eq_zero.mp hn
    have hfzero (i : I) : F i = 0 := by
      have h1 := hmargin i star
      have h2 := hmargin star i
      simp only [hxzero, hgzero, hF, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
        mul_zero, inner_zero_left, sub_zero, zero_sub] at h1 h2
      linarith
    refine ⟨fun u => m / 2 * ‖u‖ ^ 2, quadratic_objective hm hL, fun i => ?_⟩
    constructor
    · simp [hxzero, hfzero]
    · rw [hxzero, hgzero]
      simpa using (quadratic_objective (E := E) hm hL).gradient_zero
  · exact extend_strict_support_pos hε hKpos hm hL hbound hmargin hlip star hx hG hF

/-- The literal statement of Lemma `extend` permits any real K.  A
nonpositive declared Lipschitz bound reduces to the zero-bound case. -/
theorem extend_strict_support_real {x G : I → E} {F : I → ℝ} {ε K m L : ℝ}
    (hε : 0 < ε) (hm : 0 < m) (hL : m < L)
    (hbound : m + K ^ 2 / (2 * ε) ≤ L)
    (hmargin : ∀ i j, ε * ‖x i - x j‖ ^ 2 ≤ F i - F j - ⟪G j, x i - x j⟫_ℝ)
    (hlip : ∀ i j, ‖G i - G j‖ ≤ K * ‖x i - x j‖)
    (star : I) (hx : x star = 0) (hG : G star = 0) (hF : F star = 0) :
    ∃ f : E → ℝ, polyak.CenteredSmoothStronglyConvex m L f ∧
      ∀ i, f (x i) = F i + m / 2 * ‖x i‖ ^ 2 ∧
        gradient f (x i) = m • x i + G i := by
  by_cases hK : 0 ≤ K
  · exact extend_strict_support hε hK hm hL hbound hmargin hlip star hx hG hF
  · have hlip0 (i j : I) : ‖G i - G j‖ ≤ 0 * ‖x i - x j‖ := by
      rw [zero_mul]
      exact (hlip i j).trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK) (norm_nonneg _))
    exact extend_strict_support hε (K := 0) le_rfl hm hL (by simpa using hL.le)
      hmargin hlip0 star hx hG hF

end nesterov.Flow

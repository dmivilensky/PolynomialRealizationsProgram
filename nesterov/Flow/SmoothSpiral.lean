import nesterov.Flow.OrbitInterpolation

/-!
Article: Theorem `flow`(c), construction from the strict spread program.
Use: turn uniform real-lag margins into one actual global smooth strongly
convex objective realizing the entire infinite orbit, with exact norm decay.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {J : Type*} [Fintype J]

/-- The strict margins used in the proof of Theorem flow(c). -/
structure Spectrum.StrictProgram (ν : Spectrum J) (θ m c ε : ℝ) : Prop where
  epsilon_pos : 0 < ε
  forward : ∀ q : ℝ, 0 < q →
    ε * (∑ j, ν.weight j * kernelA c (ν.frequency j) q) ≤
      ∑ j, ν.weight j * forwardKernel θ m c (ν.frequency j) q
  backward : ∀ q : ℝ, 0 < q →
    ε * (∑ j, ν.weight j * kernelA c (ν.frequency j) q) ≤
      ∑ j, ν.weight j * backwardKernel θ m c (ν.frequency j) q
  minimizer : 1 ≤ (3 * c - θ) * (∑ j, ν.weight j * ν.frequency j ^ 2) - c * delta θ m c

theorem Spectrum.strictProgram_feasible (ν : Spectrum J) {θ m c ε : ℝ}
    (h : ν.StrictProgram θ m c ε) : ν.Feasible θ m c := by
  have hn (q : ℝ) : 0 ≤ ε * (∑ j, ν.weight j * kernelA c (ν.frequency j) q) :=
    mul_nonneg h.epsilon_pos.le (Finset.sum_nonneg fun j _ =>
      mul_nonneg (ν.weight_nonneg j) (kernelA_nonneg _ _ _))
  exact ⟨fun q hq => (hn q).trans (h.forward q hq),
    fun q hq => (hn q).trans (h.backward q hq), by linarith [h.minimizer]⟩

theorem Spectrum.strict_support_margin (ν : Spectrum J) {θ m c ε : ℝ}
    (hc : 0 < c) (hct : c ≤ θ / 2) (h : ν.StrictProgram θ m c ε) :
    ∀ i j : OrbitIndex, min (ε / 2) (1 / (2 * c)) * ‖ν.jetPoint c i - ν.jetPoint c j‖ ^ 2 ≤
      ν.jetValue θ m c i - ν.jetValue θ m c j -
        ⟪ν.jetGradient θ m c j, ν.jetPoint c i - ν.jetPoint c j⟫_ℝ := by
  let e := min (ε / 2) (1 / (2 * c))
  have he1 : 2 * e ≤ ε := by dsimp [e]; linarith [min_le_left (ε / 2) (1 / (2 * c))]
  have he2 : e ≤ 1 / (2 * c) := min_le_right _ _
  have hgap (t : ℝ) : e * ‖ν.orbit c t‖ ^ 2 ≤
      ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ - ν.orbitValue θ m c t := by
    rw [ν.orbit_norm_sq, ν.minimizer_gap hc, ν.minimizer_gap_moment hc]
    have hm := (div_le_div_iff_of_pos_right (show 0 < 2 * c by positivity)).mpr h.minimizer
    have he := mul_le_mul_of_nonneg_left (he2.trans hm) (Real.exp_pos (-2 * c * t)).le
    nlinarith
  have hlag (t q : ℝ) (hq : 0 < q) :
      e * ‖ν.orbit c (t + q) - ν.orbit c t‖ ^ 2 ≤
        ν.orbitValue θ m c (t + q) - ν.orbitValue θ m c t -
          ⟪ν.forcedGradient θ m c t, ν.orbit c (t + q) - ν.orbit c t⟫_ℝ ∧
      e * ‖ν.orbit c t - ν.orbit c (t + q)‖ ^ 2 ≤
        ν.orbitValue θ m c t - ν.orbitValue θ m c (t + q) -
          ⟪ν.forcedGradient θ m c (t + q), ν.orbit c t - ν.orbit c (t + q)⟫_ℝ := by
    rw [ν.forward_slack hc, ν.backward_slack hc, norm_sub_rev (ν.orbit c t), ν.orbit_distance_sq]
    have hA : 0 ≤ ∑ j, ν.weight j * kernelA c (ν.frequency j) q :=
      Finset.sum_nonneg fun j _ => mul_nonneg (ν.weight_nonneg j) (kernelA_nonneg _ _ _)
    have hbase := mul_le_mul_of_nonneg_right he1 hA
    have hf := mul_le_mul_of_nonneg_left (hbase.trans (h.forward q hq))
      (Real.exp_pos (-2 * c * t - c * q)).le
    have hb := mul_le_mul_of_nonneg_left (hbase.trans (h.backward q hq))
      (Real.exp_pos (-2 * c * t - c * q)).le
    constructor <;> nlinarith
  intro i j
  cases i with
  | none =>
    cases j with
    | none => simp [jetPoint, jetGradient, jetValue]
    | some t =>
      change e * ‖0 - ν.orbit c t‖ ^ 2 ≤ 0 - ν.orbitValue θ m c t -
        ⟪ν.forcedGradient θ m c t, 0 - ν.orbit c t⟫_ℝ
      simp only [zero_sub, norm_neg, inner_neg_right]
      linarith [hgap t]
  | some s =>
    cases j with
    | none =>
      change e * ‖ν.orbit c s - 0‖ ^ 2 ≤ ν.orbitValue θ m c s - 0 - ⟪(0 : EuclideanSpace ℂ J), _⟫_ℝ
      simp only [sub_zero, inner_zero_left]
      exact (hgap s).trans (ν.value_ge_minimizer_gap hc hct s)
    | some t =>
      change e * ‖ν.orbit c s - ν.orbit c t‖ ^ 2 ≤ ν.orbitValue θ m c s -
        ν.orbitValue θ m c t - ⟪ν.forcedGradient θ m c t, ν.orbit c s - ν.orbit c t⟫_ℝ
      rcases lt_trichotomy (t : ℝ) (s : ℝ) with hlt | heq | hgt
      · simpa only [add_sub_cancel] using (hlag t ((s : ℝ) - t) (sub_pos.mpr hlt)).1
      · have heq' : t = s := Subtype.ext heq
        subst t
        simp
      · simpa only [add_sub_cancel] using (hlag s ((t : ℝ) - s) (sub_pos.mpr hgt)).2

theorem Spectrum.jetGradient_lipschitz (ν : Spectrum J) (θ m c : ℝ) (i j : OrbitIndex) :
    ‖ν.jetGradient θ m c i - ν.jetGradient θ m c j‖ ≤
      ‖ν.gradientOperator θ m c‖ * ‖ν.jetPoint c i - ν.jetPoint c j‖ := by
  have he (i : OrbitIndex) : ν.jetGradient θ m c i = ν.gradientOperator θ m c (ν.jetPoint c i) := by
    cases i with
    | none => simp [jetGradient, jetPoint]
    | some t => rfl
  rw [he i, he j, ← map_sub]
  exact (ν.gradientOperator θ m c).le_opNorm _

/-- A strict continuous-lag program yields one genuine smooth strongly convex
objective and a solution with the exact state norm scaling in Theorem flow(c). -/
theorem Spectrum.exists_smooth_spiral (ν : Spectrum J) {θ m c ε : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hct : c ≤ θ / 2) (h : ν.StrictProgram θ m c ε) :
    ∃ (L : ℝ) (f : EuclideanSpace ℂ J → ℝ), m < L ∧
      polyak.CenteredSmoothStronglyConvex m L f ∧
      IsSolution θ f (ν.orbit c) (ν.velocity c) ∧
      (∀ t : ℝ, 0 ≤ t → f (ν.orbit c t) = ν.orbitValue θ m c t + m / 2 * ‖ν.orbit c t‖ ^ 2) ∧
      (∀ t : ℝ, ‖ν.orbit c t‖ = Real.exp (-c * t)) ∧
      (∀ t : ℝ, ‖ν.velocity c t‖ = Real.exp (-c * t) * ‖ν.velocity c 0‖) := by
  let e := min (ε / 2) (1 / (2 * c))
  have he : 0 < e := lt_min (by linarith [h.epsilon_pos]) (by positivity)
  let K := ‖ν.gradientOperator θ m c‖
  let L := m + K ^ 2 / (2 * e) + 1
  have hL : m < L := by
    have hn : 0 ≤ K ^ 2 / (2 * e) := by positivity
    dsimp [L]
    linarith
  obtain ⟨f, hf, hdata⟩ := extend_strict_support he (norm_nonneg _) hm hL
    (show m + K ^ 2 / (2 * e) ≤ L by dsimp [L]; linarith)
    (ν.strict_support_margin hc hct h) (ν.jetGradient_lipschitz θ m c)
    none rfl rfl rfl
  refine ⟨L, f, hL, hf, ⟨?_, ?_⟩, ?_, ν.orbit_norm c, ?_⟩
  · intro t _
    exact ν.hasDerivAt_orbit c t
  · intro t ht
    have hg := (hdata (some ⟨t, ht⟩)).2
    change gradient f (ν.orbit c t) = m • ν.orbit c t + ν.forcedGradient θ m c t at hg
    rw [hg]
    have ho := ν.orbit_ode θ m c t
    have heq : -θ • ν.velocity c t - (m • ν.orbit c t + ν.forcedGradient θ m c t) =
        ν.acceleration c t := by linear_combination (norm := module) -ho
    rw [heq]
    exact ν.hasDerivAt_velocity c t
  · intro t ht
    exact (hdata (some ⟨t, ht⟩)).1
  · intro t
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
    rw [mul_pow, ν.velocity_norm_sq c t, ν.velocity_norm_sq c 0]
    simp only [mul_zero, Real.exp_zero, one_mul]
    have he2 : Real.exp (-c * t) ^ 2 = Real.exp (-2 * c * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he2]

end nesterov.Flow

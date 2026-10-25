import polyak.FareyPlateau.LargeCurvature.FarEstimates
import polyak.FareyPlateau.LargeCurvature.IndexedCertificate
import polyak.FareyPlateau.LargeCurvature.SourceCurvature

/-! The far-zone profile bounds and the exact cotangent factorization of
the actual indexed symbol, including both frequency endpoints. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels ModeLocking Set
open scoped BigOperators

theorem profile_far_upper (q : Tuning) {c₀ h₀ a D M ε c : ℝ}
    (he : Chart.coefficients q = edgeCoefficients c₀ h₀ a D)
    (hc₀ : |c₀| ≤ 1) (hc : |c| ≤ 1) (hM : 0 ≤ M) (hD : |D| ≤ M)
    (ha : 0 ≤ a) (hε : 0 ≤ ε) (hd : ε ≤ |c - c₀|)
    (hlarge : 2 * (h₀ + 2 + 2 * M) < a * ε^2) :
    q.Xi c ≤ -(a * ε^2) / 2 := by
  have hsum : |c - c₀| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hD' := abs_le.mp hD
  have hcoef : |1 + D| ≤ 1 + M := abs_le.mpr ⟨by linarith [hD'.1], by linarith [hD'.2]⟩
  have hlinear : (1 + D) * (c - c₀) ≤ 2 * (1 + M) := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact (mul_le_mul hcoef hsum (abs_nonneg _) (by linarith)).trans_eq (by ring)
  have hsq : ε^2 ≤ (c - c₀)^2 := by
    have hh := (sq_le_sq₀ hε (abs_nonneg _)).mpr hd
    rwa [sq_abs] at hh
  have hm := mul_le_mul_of_nonneg_left hsq ha
  rw [← Chart.eval_coefficients, he, edgeCoefficients_eval]
  nlinarith

theorem indexedSymbol_cotangent (q : Tuning) (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    {ω : ℝ} (hω : ω ∈ Ioo (0 : ℝ) Real.pi) :
    indexedSymbol q 0 n w ω =
      (Real.sin (q.angle ω) / Real.sin ω) *
        (q.Xi (Real.cos ω) * Symbols.denominator n w ω - Real.sin ω * sineNumerator n w ω) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hθ := q.angle_mem hω
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hcot := q.cot_angle hω
  have hcos : Real.cos (q.angle ω) = Real.sin (q.angle ω) * q.Xi (Real.cos ω) / Real.sin ω := by
    field_simp [hs.ne', hsin.ne'] at hcot ⊢
    nlinarith
  have hpoint (i : Fin 3) : lagExtension q 0 (n i) ω =
      (Real.sin (q.angle ω) / Real.sin ω) *
        (q.Xi (Real.cos ω) * (1 - Real.cos ((n i : ℝ) * ω)) -
          Real.sin ω * Real.sin ((n i : ℝ) * ω)) := by
    let ξ : Frequency := ⟨ω, hω.1.le, hω.2.le⟩
    change lagExtension q 0 (n i) ξ = _
    rw [lagExtension_actual, Geometry.shiftedCurve_zero]
    unfold Curve.lag
    rw [tuningCurve_apply, Real.cos_sub, hcos]
    field_simp
    ring
  unfold indexedSymbol Symbols.denominator sineNumerator
  simp only [hpoint, Fin.sum_univ_succ]
  ring

theorem indexedSymbol_at_pi (q : Tuning) (n : Fin 3 → ℤ) (w : Fin 3 → ℝ) :
    indexedSymbol q 0 n w Real.pi = -Symbols.denominator n w Real.pi := by
  have hpoint (i : Fin 3) : lagExtension q 0 (n i) Real.pi = -(1 - Real.cos ((n i : ℝ) * Real.pi)) := by
    change lagExtension q 0 (n i) frequencyPi = _
    rw [lagExtension_actual]
    unfold Curve.lag
    rw [Curve.at_pi, Real.cos_pi, Real.cos_sub, Real.cos_pi, Real.sin_pi]
    change -1 - (Real.cos ((n i : ℝ) * Real.pi) * -1 + Real.sin ((n i : ℝ) * Real.pi) * 0) = _
    ring
  simp only [indexedSymbol, hpoint, mul_neg, Finset.sum_neg_distrib, Symbols.denominator]

theorem negative_bracket_large {P Q X A N s : ℝ}
    (hN : 0 < N) (hP : 1 / (24 * N^2) ≤ P) (hQ : |Q| ≤ 1)
    (hs : |s| ≤ 1) (hX : X ≤ -A / 2) (hA : 48 * N^2 < A) :
    X * P - s * Q < 0 := by
  have hAp : 0 < A := lt_of_le_of_lt (by positivity : 0 ≤ 48 * N^2) hA
  have hPp : 0 < P := (div_pos (by norm_num) (by positivity)).trans_le hP
  have hmul := mul_le_mul_of_nonneg_right hX hPp.le
  have hfloor : 1 < A / 2 * P := by
    have h₁ := mul_le_mul_of_nonneg_left hP (show 0 ≤ A / 2 by positivity)
    have h₂ : 1 < (A / 2) / (24 * N^2) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
    have he : A / 2 * (1 / (24 * N^2)) = (A / 2) / (24 * N^2) := by ring
    rw [he] at h₁
    exact h₂.trans_le h₁
  have hprod : |s * Q| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg Q]
  nlinarith [neg_le_abs (s * Q)]

theorem negative_bracket_small {P Q X A N k ω s : ℝ}
    (hk : 0 < k) (hN : 0 < N) (hω : 0 < ω)
    (hP : k^2 * ω^2 / (3 * Real.pi^2) ≤ P) (hQ : |Q| ≤ N * ω)
    (hs : |s| ≤ ω) (hX : X ≤ -A / 2)
    (hA : 6 * Real.pi^2 * N / k^2 < A) : X * P - s * Q < 0 := by
  have hAp : 0 < A := (div_pos (by positivity) (sq_pos_of_pos hk)).trans hA
  have hPp : 0 < P := (div_pos (by positivity) (by positivity)).trans_le hP
  have hmul := mul_le_mul_of_nonneg_right hX hPp.le
  have hthreshold : N < A * k^2 / (6 * Real.pi^2) := by
    have hh := (div_lt_iff₀ (sq_pos_of_pos hk)).mp hA
    exact (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hfloor : N * ω^2 < A / 2 * P := by
    have h₁ := mul_le_mul_of_nonneg_left hP (show 0 ≤ A / 2 by positivity)
    have h₂ := mul_lt_mul_of_pos_right hthreshold (sq_pos_of_pos hω)
    have he : A / 2 * (k^2 * ω^2 / (3 * Real.pi^2)) =
      (A * k^2 / (6 * Real.pi^2)) * ω^2 := by ring
    rw [he] at h₁
    exact h₂.trans_le h₁
  have hprod : |s * Q| ≤ N * ω^2 := by
    rw [abs_mul]
    have hh := mul_le_mul hs hQ (abs_nonneg _) hω.le
    nlinarith only [hh]
  nlinarith [neg_le_abs (s * Q)]

end polyak.FareyPlateau.LargeCurvature

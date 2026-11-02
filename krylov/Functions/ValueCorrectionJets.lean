import krylov.Functions.ValueDefectSecondKernel

/-!
Article: main_krylov, prop:Fcycle(i), the model-metric split and normalized
function-value diagonal jet.
Use: quantify the split from genuine secant/reference errors, and transfer
the independently derived actual cubic value defect through its normalization.
Source: dual pairing, continuous trilinear algebra, and the real quotient.
-/

namespace krylov.Functions
noncomputable section
open Real
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual model-metric split differs from one-half by the endpoint displacement pairing.
Article: main_krylov, prop:Fcycle(i), lambda^Y on a quadratic reference. -/
theorem covectorSplit_sub_half (y : E →L[ℝ] ℝ) (a s x : E) (hy : y s ≠ 0) :
    covectorSplit y a s x - 1 / 2 = y (x - (a + s)) / y s := by
  have he : x - (a + (1 / 2 : ℝ) • s) = x - (a + s) + (1 / 2 : ℝ) • s := by module
  rw [covectorSplit, he, map_add, map_smul]
  field_simp
  ring

/-- Genuine quadratic secant and endpoint shadows give the actual split its linear error bound.
Article: main_krylov, prop:Fcycle(i), lambda_a=1/2+O(e_c).
The premises concern raw observed vectors, actual reference conjugacy and
an actual positive secant denominator; they contain no split estimate. -/
theorem covectorSplit_half_bound (y y₀ a s x b₀ : E)
    (ε Cy Cb My Mb c : ℝ) (hε : 0 < ε) (hc : 0 < c)
    (hCy : 0 ≤ Cy) (hCb : 0 ≤ Cb) (hMy : 0 ≤ My) (hMb : 0 ≤ Mb)
    (hy : ‖y - ε • y₀‖ ≤ Cy * ε ^ 2)
    (hb : ‖(x - (a + s)) - ε • b₀‖ ≤ Cb * ε ^ 2)
    (hyn : ‖y‖ ≤ My * ε) (hbn : ‖b₀‖ ≤ Mb)
    (horth : inner ℝ y₀ b₀ = 0) (hden : c * ε ^ 2 ≤ inner ℝ y s) :
    |covectorSplit (innerSL ℝ y) a s x - 1 / 2| ≤
      ((My * Cb + Cy * Mb) / c) * ε := by
  have hd : 0 < inner ℝ y s := (mul_pos hc (sq_pos_of_pos hε)).trans_le hden
  rw [covectorSplit_sub_half _ a s x (by simpa only [innerSL_apply_apply] using hd.ne')]
  simp only [innerSL_apply_apply]
  rw [abs_div, abs_of_pos hd]
  have he : inner ℝ y (x - (a + s)) =
      inner ℝ y ((x - (a + s)) - ε • b₀) + inner ℝ (y - ε • y₀) (ε • b₀) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, horth, mul_zero, sub_zero]
    ring
  have hnum : |inner ℝ y (x - (a + s))| ≤ (My * Cb + Cy * Mb) * ε ^ 3 := by
    rw [he]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)).trans
    have hεbn : ‖ε • b₀‖ ≤ ε * Mb := by
      rw [norm_smul, Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left hbn hε.le
    exact (add_le_add
      (mul_le_mul hyn hb (norm_nonneg _) (mul_nonneg hMy hε.le))
      (mul_le_mul hy hεbn (norm_nonneg _) (mul_nonneg hCy (sq_nonneg ε)))).trans_eq (by ring)
  apply (div_le_iff₀ hd).mpr
  have hcoeff : 0 ≤ ((My * Cb + Cy * Mb) / c) * ε := by positivity
  calc
    _ ≤ (My * Cb + Cy * Mb) * ε ^ 3 := hnum
    _ = (((My * Cb + Cy * Mb) / c) * ε) * (c * ε ^ 2) := by field_simp
    _ ≤ (((My * Cb + Cy * Mb) / c) * ε) * inner ℝ y s :=
      mul_le_mul_of_nonneg_left hden hcoeff

/-- Actual secant and step shadows preserve their true quadratic reference energy.
Article: main_krylov, prop:Fcycle(i), deriving the observed denominator.
The estimate uses raw observed vectors and contains no split assumption. -/
theorem secant_energy_shadow (y y₀ s σ : E) (ε Cy Cs Ms My₀ : ℝ)
    (hε : 0 ≤ ε) (hCy : 0 ≤ Cy) (_hCs : 0 ≤ Cs)
    (_hMs : 0 ≤ Ms) (hMy₀ : 0 ≤ My₀)
    (hy : ‖y - ε • y₀‖ ≤ Cy * ε ^ 2) (hs : ‖s - ε • σ‖ ≤ Cs * ε ^ 2)
    (hsn : ‖s‖ ≤ Ms * ε) (hyn : ‖y₀‖ ≤ My₀) :
    |inner ℝ y s - ε ^ 2 * inner ℝ y₀ σ| ≤ (Cy * Ms + My₀ * Cs) * ε ^ 3 := by
  have he : inner ℝ y s - ε ^ 2 * inner ℝ y₀ σ =
      inner ℝ (y - ε • y₀) s + inner ℝ (ε • y₀) (s - ε • σ) := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he]
  have hεy : ‖ε • y₀‖ ≤ ε * My₀ := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left hyn hε
  calc
    _ ≤ |inner ℝ (y - ε • y₀) s| + |inner ℝ (ε • y₀) (s - ε • σ)| := abs_add_le _ _
    _ ≤ ‖y - ε • y₀‖ * ‖s‖ + ‖ε • y₀‖ * ‖s - ε • σ‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (Cy * ε ^ 2) * (Ms * ε) + (ε * My₀) * (Cs * ε ^ 2) :=
      add_le_add (mul_le_mul hy hsn (norm_nonneg _) (by positivity))
        (mul_le_mul hεy hs (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- A genuine third-derivative contraction has its actual operator norm bound.
Article: main_krylov, prop:Fcycle(i), continuous cubic substitution. -/
theorem inner_third_bound (D : E →L[ℝ] E →L[ℝ] E) (a b c : E) :
    |inner ℝ (D a b) c| ≤ ‖D‖ * ‖a‖ * ‖b‖ * ‖c‖ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (((D a).le_opNorm b).trans
        (mul_le_mul_of_nonneg_right (D.le_opNorm a) (norm_nonneg b))) (norm_nonneg c))

/-- Replacing an actual step in all three tensor slots has a quantitative genuine remainder.
Article: main_krylov, prop:Fcycle(i), physical step/reference substitution. -/
theorem inner_third_diagonal_sub_bound (D : E →L[ℝ] E →L[ℝ] E) (s v : E) :
    |inner ℝ (D s s) s - inner ℝ (D v v) v| ≤
      ‖D‖ * (‖s‖ ^ 2 + ‖v‖ * ‖s‖ + ‖v‖ ^ 2) * ‖s - v‖ := by
  have he : inner ℝ (D s s) s - inner ℝ (D v v) v =
      inner ℝ (D (s-v) s) s + inner ℝ (D v (s-v)) s + inner ℝ (D v v) (s-v) := by
    simp only [map_sub, sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |inner ℝ (D (s-v) s) s| + |inner ℝ (D v (s-v)) s| + |inner ℝ (D v v) (s-v)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖D‖ * ‖s-v‖ * ‖s‖ * ‖s‖ + ‖D‖ * ‖v‖ * ‖s-v‖ * ‖s‖ +
        ‖D‖ * ‖v‖ * ‖v‖ * ‖s-v‖ :=
      add_le_add (add_le_add (inner_third_bound D (s-v) s s) (inner_third_bound D v (s-v) s))
        (inner_third_bound D v v (s-v))
    _ = _ := by ring

/-- Cubic contractions have the expected fourth-order step-shadow error.
Article: main_krylov, prop:Fcycle(i), true cubic value-defect coefficient. -/
theorem inner_third_diagonal_shadow (D : E →L[ℝ] E →L[ℝ] E) (s σ : E)
    (ε M C : ℝ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (_hC : 0 ≤ C)
    (hs : ‖s‖ ≤ M * ε) (hσ : ‖σ‖ ≤ M) (herr : ‖s - ε • σ‖ ≤ C * ε ^ 2) :
    |inner ℝ (D s s) s - ε ^ 3 * inner ℝ (D σ σ) σ| ≤
      3 * ‖D‖ * M ^ 2 * C * ε ^ 4 := by
  have hv : ‖ε • σ‖ ≤ M * ε := by
    rw [norm_smul, Real.norm_of_nonneg hε]
    exact (mul_le_mul_of_nonneg_left hσ hε).trans_eq (mul_comm _ _)
  have hsum : ‖s‖ ^ 2 + ‖ε • σ‖ * ‖s‖ + ‖ε • σ‖ ^ 2 ≤ 3 * (M * ε) ^ 2 := by
    have hs2 := (sq_le_sq₀ (norm_nonneg s) (mul_nonneg hM hε)).mpr hs
    have hv2 := (sq_le_sq₀ (norm_nonneg (ε • σ)) (mul_nonneg hM hε)).mpr hv
    have hsv := mul_le_mul hv hs (norm_nonneg s) (mul_nonneg hM hε)
    nlinarith only [hs2, hv2, hsv]
  have hh := inner_third_diagonal_sub_bound D s (ε • σ)
  have he : inner ℝ (D (ε • σ) (ε • σ)) (ε • σ) = ε ^ 3 * inner ℝ (D σ σ) σ := by
    simp only [map_smul, smul_apply, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [he] at hh
  exact hh.trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left hsum (norm_nonneg D)) herr
    (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- The normalized observed diagonal correction inherits its exact one-half cubic jet.
Article: main_krylov, prop:Fcycle(i), Delta_H normalized by the actual start scale.
This algebraic estimate combines the independently proved defect remainder
and split bound without losing a power of the small source scale. -/
theorem normalized_value_correction_jet (δ l t ε J : ℝ) (hε : 0 < ε)
    (hδ : |δ + ε ^ 3 * t / 12| ≤ J) :
    |(-12 * l * δ) / ε ^ 2 - ε / 2 * t| ≤
      12 * |l| * J / ε ^ 2 + ε * |l - 1 / 2| * |t| := by
  have he : (-12 * l * δ) / ε ^ 2 - ε / 2 * t =
      (-12 * l / ε ^ 2) * (δ + ε ^ 3 * t / 12) + ε * (l - 1 / 2) * t := by
    field_simp
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_div, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12),
    abs_pow, abs_of_pos hε, abs_mul, abs_mul, abs_of_pos hε]
  calc
    _ ≤ (12 * |l| / ε ^ 2) * J + ε * |l - 1 / 2| * |t| :=
      add_le_add (mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 12 * |l| / ε ^ 2)) le_rfl
    _ = _ := by ring

/-- Quantitative split and true defect jets give the normalized diagonal its actual linear source jet.
Article: main_krylov, prop:Fcycle(i), the final diagonal substitution.
The same estimate yields little-o of epsilon and, for a fourth-order defect,
a quadratic remainder after normalizing by the square of the source scale. -/
theorem normalized_value_correction_bound (δ l t ε C B J : ℝ)
    (hε : 0 < ε) (he : ε ≤ 1) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hJ : 0 ≤ J)
    (hl : |l - 1 / 2| ≤ C * ε) (ht : |t| ≤ B)
    (hδ : |δ + ε ^ 3 * t / 12| ≤ J * ε ^ 3) :
    |(-12 * l * δ) / ε ^ 2 - ε / 2 * t| ≤
      12 * (C + 1) * J * ε + C * B * ε ^ 2 := by
  have hlb : |l| ≤ C + 1 := by
    have hh : |l| ≤ |l - 1 / 2| + |(1 / 2 : ℝ)| := by
      simpa only [sub_add_cancel] using abs_add_le (l - 1 / 2) (1 / 2 : ℝ)
    have hCe := mul_le_mul_of_nonneg_left he hC
    norm_num at hh
    linarith only [hh, hl, hCe]
  have hh := normalized_value_correction_jet δ l t ε (J * ε ^ 3) hε hδ
  apply hh.trans
  have hfirst : 12 * |l| * (J * ε ^ 3) / ε ^ 2 ≤ 12 * (C + 1) * J * ε := by
    have heq : 12 * |l| * (J * ε ^ 3) / ε ^ 2 = 12 * |l| * J * ε := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlb (by norm_num : (0 : ℝ) ≤ 12)) hJ)
      hε.le
  have hsecond : ε * |l - 1 / 2| * |t| ≤ C * B * ε ^ 2 := by
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left hl hε.le) ht (abs_nonneg _) (by positivity)).trans_eq (by ring)
  exact add_le_add hfirst hsecond

end
end krylov.Functions

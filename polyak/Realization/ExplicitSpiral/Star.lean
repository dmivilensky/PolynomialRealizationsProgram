import polyak.Realization.ExplicitSpiral.SmallQ
import polyak.Realization.ExplicitSpiral.StationaryTable

/-!
Article: the unchanged value at the initial point satisfies both minimizer
interpolation inequalities, with the fixed auxiliary amplitude Y=2.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the first from-rest gradient simplifies to λ/(2q)+q/2. -/
theorem multiplier_add_defect {q : ℝ} (hq : 0<q) {z : ℂ} (hz : z≠0) :
    multiplier z q+defect z q=z/((2*q : ℝ) : ℂ)+((q/2 : ℝ) : ℂ) := by
  have hqc : (q : ℂ)≠0 := by exact_mod_cast hq.ne'
  unfold multiplier defect
  push_cast
  field_simp
  ring

/-- Article: the small-q gradient defect has the uniform bound 3/5. -/
theorem small_norm_defect {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq5 : q≤1/5)
    (hF : Spiral.spiralPolynomial r q=0) : ‖defect (radialWave r) q‖≤3/5 := by
  have hqr : q/r<1 := (div_lt_one hr).mpr (root_gt_q hr hq hF)
  have hd := norm_defect_le hr hq.le (radial_wave_coordinates hr).1
  linarith

/-- Article: the large-q first gradient has norm strictly below 3/2. -/
theorem large_norm_initialGradient {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hq5 : 1/5≤q) (hF : Spiral.spiralPolynomial r q=0) :
    ‖multiplier (radialWave r) q+defect (radialWave r) q‖<3/2 := by
  have hn := (radial_wave_coordinates hr).1
  have hz : radialWave r≠0 := norm_pos_iff.mp (by rwa [hn])
  rw [multiplier_add_defect hq hz]
  have hh := norm_add_le (radialWave r/((2*q : ℝ) : ℂ)) ((q/2 : ℝ) : ℂ)
  rw [norm_div,hn,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    Real.norm_eq_abs,abs_of_pos (by positivity : 0<2*q),abs_of_pos (by positivity : 0<q/2)] at hh
  have hratio : r/(2*q)<1 := (div_lt_one (by positivity : 0<2*q)).mpr
    (root_lt_two_q hr hq hq1 hq5 hF)
  linarith

/-- Article: both exact initial minimizer inequalities hold for every κ>1. -/
theorem initialized_star_bound {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) :
    |physicalValueConstant r/4-(defect (radialWave r) q).re/2|≤
      (5-Complex.normSq (multiplier (radialWave r) q+defect (radialWave r) q))/4 := by
  obtain ⟨_,hn,hz⟩ := radial_wave_coordinates hr
  have hC := abs_physicalValueConstant_le_half hr
  by_cases hq5 : q≤1/5
  · exact small_star_bound _ _ (norm_multiplier_le_one hr hq hn hz hF)
      (small_norm_defect hr hq hq5 hF) hC
  · have hq5' : 1/5≤q := (lt_of_not_ge hq5).le
    have hb := large_norm_initialGradient hr hq hq1 hq5' hF
    have hb2 : Complex.normSq (multiplier (radialWave r) q+defect (radialWave r) q)<9/4 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (multiplier (radialWave r) q+defect (radialWave r) q)]
    have hd := (multiplier_defect_coordinates hr hq hn hz).2.2.1
    have hd0 : 0≤(defect (radialWave r) q).re := by rw [hd]; unfold Source.defectReal; positivity
    have hd1 : (defect (radialWave r) q).re≤q := by
      rw [hd,Source.defectReal]
      apply (div_le_iff₀ (by positivity : 0<2*(r^2+1))).mpr
      nlinarith [mul_nonneg hq.le (sq_nonneg r)]
    obtain ⟨hCl,hCu⟩ := abs_le.mp hC
    apply abs_le.mpr
    constructor <;> linarith

end
end polyak.Realization.ExplicitSpiral

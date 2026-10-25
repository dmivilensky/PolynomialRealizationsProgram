import polyak.Realization.ExplicitSpiral.PairCoordinates
import polyak.Realization.ExplicitSpiral.Ranges

/-!
Article: the physical master equation links the rational source to the actual
normalized Polyak multiplier and its positive minimizer reserve.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: the independently defined source gap is strictly positive. -/
theorem source_gap_pos {r : ℝ} (hr : 0<r) : 0<Source.gap r := by
  unfold Source.gap
  have hp : 0<r^2-r+1 := by nlinarith [sq_nonneg (r-1/2)]
  positivity

/-- Article: the source multiplier has the exact gap on the master-polynomial branch. -/
theorem source_multiplier_gap {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) :
    1-(Source.multiplierReal r q^2+Source.imaginarySquare r*Source.multiplierImag r q^2)=
      Source.gap r := by
  have hid : 1-(Source.multiplierReal r q^2+
      Source.imaginarySquare r*Source.multiplierImag r q^2)-Source.gap r=
      Spiral.spiralPolynomial r q*
        (q^2*r^2+q^2-2*q*r^3+2*q*r^2-2*q*r-r^4-r^2)/
          (4*q^2*r^2*(r^2+1)^2) := by
    unfold Source.multiplierReal Source.multiplierImag Source.imaginarySquare
      Source.lambdaReal Source.gap Spiral.spiralPolynomial
    field_simp
    ring
  rw [hF,zero_mul,zero_div] at hid
  linarith

/-- Article: the imaginary multiplier is precisely the spiral coefficient gG/ρ. -/
theorem source_multiplierImag_eq {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) :
    Source.multiplierImag r q=Source.gap r*Source.hyperbolic r/r := by
  have hid : Source.multiplierImag r q-Source.gap r*Source.hyperbolic r/r=
      Spiral.spiralPolynomial r q/(2*q*r^2*(r^2+1)) := by
    unfold Source.multiplierImag Source.gap Source.hyperbolic Spiral.spiralPolynomial
    field_simp
    ring
  rw [hF,zero_div] at hid
  linarith

/-- Article: actual planar multiplier norms are bounded by one, uniformly in κ. -/
theorem multiplier_gap {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r)
    (hF : Spiral.spiralPolynomial r q=0) :
    1-Complex.normSq (multiplier z q)=Source.gap r := by
  obtain ⟨hsr,hsi,_,_⟩ := multiplier_defect_coordinates hr hq hn hz
  have him := imaginarySquare_eq hn hz
  simp only [Complex.normSq_apply,← pow_two,hsr,hsi,mul_pow,him]
  exact source_multiplier_gap hr hq hF

/-- Article: the normalized planar multiplier has norm at most one. -/
theorem norm_multiplier_le_one {r q : ℝ} (hr : 0<r) (hq : 0<q) {z : ℂ}
    (hn : Complex.normSq z=r^2) (hz : z.re=Source.lambdaReal r)
    (hF : Spiral.spiralPolynomial r q=0) : ‖multiplier z q‖≤1 := by
  have hg := multiplier_gap hr hq hn hz hF
  rw [Complex.normSq_eq_norm_sq] at hg
  have hp := source_gap_pos hr
  nlinarith [norm_nonneg (multiplier z q)]

/-- Article: the exact value constant on the special spiral. -/
def physicalValueConstant (r : ℝ) : ℝ := Source.gap r*(r^2-1)/(r^2+1)

/-- Article: the unchanged planar value datum is uniformly bounded. -/
theorem abs_physicalValueConstant_le_half {r : ℝ} (hr : 0<r) :
    |physicalValueConstant r|≤1/2 := by
  have hg := source_gap_pos hr
  have hu : Source.gap r≤1/2 := by
    rw [source_gap_half]
    exact sub_le_self _ (by positivity)
  have habs : |(r^2-1)/(r^2+1)|≤1 := by
    rw [abs_div,abs_of_pos (by positivity : 0<r^2+1)]
    exact (div_le_one (by positivity : 0<r^2+1)).mpr
      (abs_le.mpr ⟨by nlinarith [sq_nonneg r],by linarith⟩)
  unfold physicalValueConstant
  rw [div_eq_mul_inv,mul_assoc,← div_eq_mul_inv,abs_mul,abs_of_pos hg]
  nlinarith

/-- Article: the inverse-wave defect has norm at most (q+q/ρ)/2. -/
theorem norm_defect_le {r q : ℝ} (_hr : 0<r) (hq : 0≤q) {z : ℂ}
    (hn : ‖z‖=r) : ‖defect z q‖≤(q+q/r)/2 := by
  have hd : defect z q=((q/2 : ℝ) : ℂ)*(1-z⁻¹) := by simp [defect]
  rw [hd,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hh : ‖1-z⁻¹‖≤1+1/r := by
    simpa only [norm_one,norm_inv,hn,one_div] using norm_sub_le (1 : ℂ) z⁻¹
  calc
    _ ≤ (q/2)*(1+1/r) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end
end polyak.Realization.ExplicitSpiral

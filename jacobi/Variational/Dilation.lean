import jacobi.Variational.Tails

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
The mass-preserving spatial dilation acts on the actual finite-energy density
domain. Its energy and root-mass normalizations and its printed L1 perturbation
bound are proved explicitly. The operator dilation also acts on arbitrary
L1 sources; strict spectral increase is proved in the importing modules.
Source: Lebesgue change of variables and radial monotonicity.
Use: the full-domain spectral dilation estimates and their variational restrictions share one source map.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set
set_option backward.isDefEq.respectTransparency false

/-- Mass-preserving concentration of an arbitrary nonnegative L1 source.
Use: the full-domain spectral dilation estimates and their variational restrictions share one source map.
Article: jacobi, Lemma D.3.
-/
def L1Source.dilate (m : L1Source) (t : ℝ) (ht : 0<t) : L1Source where
  value x := t*m.value (t*x)
  measurable := measurable_const.mul (m.measurable.comp (measurable_const.mul measurable_id))
  nonneg x := mul_nonneg ht.le (m.nonneg (t*x))
  integrable := ((integrable_comp_mul_left_iff m.value ht.ne').mpr m.integrable).const_mul t

/-- Dilation preserves the total mass of every nonnegative L1 source.
Use: the strict operator gains preserve precisely the article's original mass constraint.
Article: jacobi, Lemma D.3.
Proof: the amplitude cancels the positive spatial Jacobian. -/
theorem L1Source.dilate_mass (m : L1Source) {t : ℝ} (ht : 0<t) :
    (m.dilate t ht).mass=m.mass := by
  change (∫ x,t*m.value (t*x))=m.mass
  rw [integral_const_mul,Measure.integral_comp_mul_left,abs_of_pos (inv_pos.mpr ht),smul_eq_mul]
  change t*(t⁻¹*m.mass)=m.mass
  field_simp

/-- Mass-preserving concentration of a density by a positive spatial scale.
Use: the feasible perturbation used to prove regularity of spectral constraints.
Article: jacobi, Lemma D.3.
-/
def Density.dilate (m : Density) (t : ℝ) (ht : 0 < t) : Density where
  toL1Source := m.toL1Source.dilate t ht
  energy_integrable := by
    change Integrable (fun x => (t*m.value (t*x))^(3/2:ℝ))
    have he : (fun x => (t*m.value (t*x))^(3/2 : ℝ)) =
        (fun x => t^(3/2 : ℝ)*(m.value (t*x)^(3/2 : ℝ))) := by
      funext x
      exact Real.mul_rpow ht.le (m.nonneg _)
    rw [he]
    exact ((integrable_comp_mul_left_iff (fun x => m.value x^(3/2 : ℝ)) ht.ne').mpr
      m.energy_integrable).const_mul _

/-- Dilation preserves the actual total mass exactly.
Use: the regularity direction remains tangent to an active mass constraint.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the scalar t cancels the Lebesgue Jacobian 1/t. -/
theorem Density.dilate_mass (m : Density) {t : ℝ} (ht : 0 < t) :
    (m.dilate t ht).mass = m.mass := L1Source.dilate_mass m.toL1Source ht

/-- Dilation multiplies the actual 3/2 energy by sqrt(t).
Use: controls objective changes in the multiplier regularity argument.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: change variables and combine the 3/2 power with the Jacobian 1/t. -/
theorem Density.dilate_energy (m : Density) {t : ℝ} (ht : 0 < t) :
    (m.dilate t ht).energy = Real.sqrt t*m.energy := by
  -- Separate the scalar power identity from the unchanged energy integrand.
  change (∫ x, (t*m.value (t*x))^(3/2 : ℝ)) = _
  simp_rw [Real.mul_rpow ht.le (m.nonneg _)]
  rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x => m.value x^(3/2 : ℝ)), abs_of_pos (inv_pos.mpr ht), smul_eq_mul]
  have he : t^(3/2 : ℝ) = t*Real.sqrt t := by
    rw [show (3/2 : ℝ)=1+1/2 by norm_num, Real.rpow_add ht, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [he]
  change (t*Real.sqrt t)*(t⁻¹*m.energy) = _
  field_simp

/-- Integrable root mass remains integrable under positive dilation.
Use: licenses the real-integral normalization of a root-mass constraint.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: factor sqrt(t) from sqrt(m_t) and apply the Lebesgue change of variables. -/
theorem Density.dilate_root_integrable (m : Density) {t : ℝ} (ht : 0 < t)
    (hr : Integrable (fun x => Real.sqrt (m.value x))) :
    Integrable (fun x => Real.sqrt ((m.dilate t ht).value x)) := by
  change Integrable (fun x => Real.sqrt (t*m.value (t*x)))
  simp_rw [Real.sqrt_mul ht.le]
  exact ((integrable_comp_mul_left_iff _ ht.ne').mpr hr).const_mul _

/-- The root-mass real integral scales by 1/sqrt(t).
Use: dilation preserves the upper root-mass constraint while increasing concentration.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: sqrt(t)/t=1/sqrt(t), since the positive square root has square t. -/
theorem Density.dilate_root_integral (m : Density) {t : ℝ} (ht : 0 < t) :
    (∫ x, Real.sqrt ((m.dilate t ht).value x)) =
      (Real.sqrt t)⁻¹*(∫ x, Real.sqrt (m.value x)) := by
  -- The square-root factor and the Jacobian combine before the integral is evaluated.
  change (∫ x, Real.sqrt (t*m.value (t*x))) = _
  simp_rw [Real.sqrt_mul ht.le]
  rw [integral_const_mul, Measure.integral_comp_mul_left
    (fun x => Real.sqrt (m.value x)), abs_of_pos (inv_pos.mpr ht), smul_eq_mul]
  have hs := Real.sq_sqrt ht.le
  have hn := (Real.sqrt_pos.mpr ht).ne'
  have he : Real.sqrt t*t⁻¹ = (Real.sqrt t)⁻¹ := by
    field_simp
    exact hs
  rw [← mul_assoc, he]

/-- The dilation of a symmetric decreasing density remains symmetric decreasing.
Use: the constraint-regularity perturbations stay in the rearranged class.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: positive multiplication preserves half-line order and evenness. -/
theorem SymmetricDecreasing.dilate {m : L1Source} (hs : SymmetricDecreasing m.value)
    {t : ℝ} (ht : 0 < t) : SymmetricDecreasing (m.dilate t ht).value where
  even x := by change t*m.value (t*(-x)) = _; rw [mul_neg, hs.even]; rfl
  decreasing := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left
      (hs.decreasing (mul_pos ht hx) (mul_pos ht hy)
        (mul_le_mul_of_nonneg_left hxy ht.le)) ht.le

/-- Concentration moves every point radially outward in the undilated density.
Use: the one-sided difference in the L1 bound has a known sign.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: compare the two absolute radii and use radial monotonicity. -/
theorem SymmetricDecreasing.at_mul_le {m : ℝ → ℝ} (hs : SymmetricDecreasing m)
    {t : ℝ} (ht : 1 ≤ t) (x : ℝ) : m (t*x) ≤ m x := by
  -- Compare strictly positive radii; the unconstrained origin is fixed by dilation.
  by_cases hx : x = 0
  · simp only [hx, mul_zero, le_refl]
  calc
    m (t*x) = m |t*x| := (hs.abs_eq _).symm
    _ ≤ m |x| := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ t)]
      have h0 : 0 < t*|x| := mul_pos (by linarith : 0 < t) (abs_pos.mpr hx)
      exact hs.decreasing (abs_pos.mpr hx) h0 (by nlinarith [abs_nonneg x])
    _ = m x := hs.abs_eq x

/-- The printed L1 perturbation bound for the actual mass-preserving dilation.
Use: the spectral first-variation remainder is quadratic along the regularity direction.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: split t m(tx)-m(x) into its amplitude and radial parts, integrate their
nonnegative bounds and use the exact mass change of variables. -/
theorem dilation_l1 (m : L1Source) (hs : SymmetricDecreasing m.value) {t : ℝ} (ht : 1 ≤ t) :
    (∫ x, |(m.dilate t (by linarith)).value x-m.value x|) ≤ 2*m.mass*(t-1) := by
  -- The radial part has a fixed sign, so the triangle majorant has an exact integral.
  have ht0 : 0 < t := by linarith
  have hcomp := (integrable_comp_mul_left_iff m.value ht0.ne').mpr m.integrable
  have hbound (x : ℝ) : |t*m.value (t*x)-m.value x| ≤
      (t-1)*m.value (t*x)+(m.value x-m.value (t*x)) := by
    have hrad := hs.at_mul_le ht x
    calc
      _ = |(t-1)*m.value (t*x)-(m.value x-m.value (t*x))| := by congr 1; ring
      _ ≤ |(t-1)*m.value (t*x)|+|m.value x-m.value (t*x)| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr ht) (m.nonneg _)),
        abs_of_nonneg (sub_nonneg.mpr hrad)]
  have h := integral_mono_ae ((m.dilate t ht0).integrable.sub m.integrable).abs
    ((hcomp.const_mul (t-1)).add (m.integrable.sub hcomp)) (Filter.Eventually.of_forall hbound)
  change (∫ x, |(m.dilate t ht0).value x-m.value x|) ≤
    ∫ x, (t-1)*m.value (t*x)+(m.value x-m.value (t*x)) at h
  have ha := integral_add (hcomp.const_mul (t-1)) (m.integrable.sub hcomp)
  have hb := integral_sub m.integrable hcomp
  dsimp only [Pi.add_apply, Pi.sub_apply] at ha hb
  rw [ha, integral_const_mul, hb, Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr ht0), smul_eq_mul] at h
  change (∫ x, |(m.dilate t ht0).value x-m.value x|) ≤ _
  apply h.trans
  change (t-1)*(t⁻¹*m.mass)+(m.mass-t⁻¹*m.mass) ≤ 2*m.mass*(t-1)
  have hM : 0 ≤ m.mass := integral_nonneg m.nonneg
  have hi : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht
  calc
    _ = 2*m.mass*((t-1)*t⁻¹) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (sub_nonneg.mpr ht) hi) (by positivity)

end
end jacobi.Variational

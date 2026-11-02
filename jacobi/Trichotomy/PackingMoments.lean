import jacobi.Trichotomy.PackingSubstitution

/-!
Article: jacobi, Proposition 2.2.
The intrinsic-coordinate Jacobian evaluates the original mass, root
mass and energy exactly. Their integrability is proved before each
integral is identified; neither compact support nor a tail estimate is
assumed in this common construction for every alpha>-1.
Use: packedDensity_mass and packedDensity_energy reuse exactly the already proved original spectral-profile integrals.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
attribute [local instance] Measure.Subtype.measureSpace

/-- Integrating a function of the true profile over its real physical interior equals integration over the original closed unit subtype.
Use: packedDensity_mass and packedDensity_energy reuse exactly the already proved original spectral-profile integrals.
Article: jacobi, Proposition 2.2.
Proof: the two endpoints have zero Lebesgue measure, and the canonical real profile agrees with the original at every physical point. -/
theorem physicalProfile_integral (a : ℝ) (ha : -1<a) (f : ℝ → ℝ) :
    (∫ t in Ioo (0:ℝ) 1,f (physicalProfile a ha t))=
      ∫ t : Interval,f (persymmetricProfile a ha t) := by
  rw [← integral_Icc_eq_integral_Ioo,← integral_subtype measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => congrArg f (physicalProfile_eq a ha t.property))

/-- The genuine packed persymmetric density has finite ordinary mass for every original order.
Use: packedDensity_mass supplies the source mass identity with actual integrability, not a totalized Bochner value.
Article: jacobi, Proposition 2.2.
Proof: its actual Jacobian integrand is phi_alpha, a continuous function on the compact physical interval. -/
theorem packedDensity_integrable (a : ℝ) (ha : -1<a) : Integrable (packedDensity a ha) := by
  apply (packed_composition_integrable_iff a ha id rfl).mpr
  apply ((physicalProfile_continuous a ha).integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
    (fun t ht => ?_) measurableSet_Ioo
  dsimp only [id_eq]
  field_simp [(physicalProfile_pos a ha ht).ne']

/-- The actual centered packed persymmetric density has precisely the original prescribed Bessel mass.
Use: Proposition C.4 and later variational comparisons concern a genuine density with the source mass M.
Article: jacobi, Proposition 2.2.
Proof: the actual Jacobian cancels one profile factor. The original spectral-profile integral was already evaluated by the full normalized basis and first Rayleigh sum. -/
theorem packedDensity_mass (a : ℝ) (ha : -1<a) :
    (∫ x : ℝ,packedDensity a ha x)=1/(2*(a+1)) := by
  -- The actual whole-line density integral is reduced to the already normalized original spectral profile integral.
  change (∫ x : ℝ,id (packedDensity a ha x))=1/(2*(a+1))
  rw [packed_composition_integral a ha id rfl]
  calc
    _ = ∫ t in Ioo (0:ℝ) 1,physicalProfile a ha t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only [id_eq]
      field_simp [(physicalProfile_pos a ha ht).ne']
    _ = _ := (physicalProfile_integral a ha id).trans (persymmetricProfile_integral a ha)

/-- The square root of the actual packed density is integrable for every original order.
Use: packedDensity_root_mass is a genuine finite root-mass identity with no separate tail premise.
Article: jacobi, Proposition 2.2.
Proof: the actual Jacobian integrand is identically one on the physical interval, since the original profile is positive there. -/
theorem packedDensity_root_integrable (a : ℝ) (ha : -1<a) :
    Integrable (fun x : ℝ => sqrt (packedDensity a ha x)) := by
  apply (packed_composition_integrable_iff a ha sqrt (by simp)).mpr
  apply (integrableOn_const (s := Ioo (0:ℝ) 1) (by simp) (C := (1:ℝ))).congr_fun
    (fun t ht => ?_) measurableSet_Ioo
  rw [Real.sqrt_sq (physicalProfile_pos a ha ht).le]
  field_simp [(physicalProfile_pos a ha ht).ne']

/-- The actual packed density has exactly root mass one throughout the complete original order range.
Use: the source packing belongs to the same root-mass normalized variational class as the finite packings.
Article: jacobi, Proposition 2.2.
Proof: its genuine Jacobian cancels the positive square root of the original profile square, leaving the length of the physical unit interval. -/
theorem packedDensity_root_mass (a : ℝ) (ha : -1<a) :
    (∫ x : ℝ,sqrt (packedDensity a ha x))=1 := by
  -- The positive original profile selects the square-root branch before cancellation in the genuine Jacobian.
  rw [packed_composition_integral a ha sqrt (by simp)]
  calc
    _ = ∫ t in Ioo (0:ℝ) 1,(1:ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [Real.sqrt_sq (physicalProfile_pos a ha ht).le]
      field_simp [(physicalProfile_pos a ha ht).ne']
    _ = 1 := by simp

/-- The literal three-halves power of a nonnegative profile square is its cube.
Use: packedDensity_energy_integrable and packedDensity_energy simplify the true source energy Jacobian without a convention about fractional powers.
Article: jacobi, Proposition 2.2.
Proof: combine positive-base real powers and evaluate the resulting integer power; zero is included by nonnegativity. -/
theorem square_three_halves {u : ℝ} (hu : 0≤u) : (u^2)^((3:ℝ)/2)=u^3 := by
  rw [← Real.rpow_two u,← Real.rpow_mul hu]
  norm_num

/-- The actual packed density has finite three-halves energy for every original order.
Use: packedDensity_energy identifies the source c_star as a genuine density energy, independently of all support and tail calculations.
Article: jacobi, Proposition 2.2.
Proof: the positive Jacobian reduces its actual integrand to phi_alpha squared, continuous on the compact original physical interval. -/
theorem packedDensity_energy_integrable (a : ℝ) (ha : -1<a) :
    Integrable (fun x : ℝ => (packedDensity a ha x)^((3:ℝ)/2)) := by
  apply (packed_composition_integrable_iff a ha (fun u => u^((3:ℝ)/2)) (by norm_num)).mpr
  apply (((physicalProfile_continuous a ha).pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
    (fun t ht => ?_) measurableSet_Ioo
  dsimp only [Pi.pow_apply]
  rw [square_three_halves (physicalProfile_pos a ha ht).le]
  field_simp [(physicalProfile_pos a ha ht).ne']

/-- The genuine packed persymmetric density has energy exactly the original spectral persymmetric constant.
Use: the source endpoint packing attains the same c_star appearing in the actual finite persymmetric limit and in Theorem 4.2.
Article: jacobi, Proposition 2.2.
Proof: the original positive Jacobian cancels one profile factor from the cube. The remaining original squared-profile integral is exactly the defining genuine c_star. -/
theorem packedDensity_energy (a : ℝ) (ha : -1<a) :
    (∫ x : ℝ,(packedDensity a ha x)^((3:ℝ)/2))=persymmetricConstant a ha := by
  -- The actual energy integrand reduces to the same squared original profile defining c_star.
  rw [packed_composition_integral a ha (fun u => u^((3:ℝ)/2)) (by norm_num)]
  calc
    _ = ∫ t in Ioo (0:ℝ) 1,(physicalProfile a ha t)^2 := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
      rw [square_three_halves (physicalProfile_pos a ha ht).le]
      field_simp [(physicalProfile_pos a ha ht).ne']
    _ = _ := physicalProfile_integral a ha (fun u => u^2)

end
end jacobi.Trichotomy

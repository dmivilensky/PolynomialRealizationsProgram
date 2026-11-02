import jacobi.Trichotomy.PackedDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
Article: jacobi, Proposition 2.2.
The derivative and injectivity of the original coordinate give the
whole-line substitution for its genuinely constructed density. The
integrability equivalence is proved separately, so the source's finite
moments do not rely on a totalized nonintegrable integral identity.
Use: packedDensity_integrable, packedDensity_root_integrable and packedDensity_energy_integrable prove finiteness before the three moments are evaluated.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan

/-- Integrability of any zero-preserving function of the actual packed density is equivalent to integrability of its literal profile Jacobian expression.
Use: packedDensity_integrable, packedDensity_root_integrable and packedDensity_energy_integrable prove finiteness before the three moments are evaluated.
Article: jacobi, Proposition 2.2.
Proof: replace the whole-line function by its indicator on the actual coordinate image. Apply the community injective one-dimensional Jacobian integrability theorem and use the independently proved actual inverse-coordinate identity and positive Jacobian. -/
theorem packed_composition_integrable_iff (a : ℝ) (ha : -1<a) (f : ℝ → ℝ) (hf : f 0=0) :
    Integrable (fun x => f (packedDensity a ha x)) ↔
      IntegrableOn (fun t => (1/physicalProfile a ha t)*f ((physicalProfile a ha t)^2)) (Ioo (0:ℝ) 1) := by
  -- This equivalence retains actual integrability, rather than merely comparing totalized Bochner integrals.
  have hind : (fun x => f (packedDensity a ha x))=
      (packingImage a ha).indicator (fun x => f (packedDensity a ha x)) := by
    ext x
    by_cases hx : x∈packingImage a ha
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,packedDensity_zero_outside a ha hx,hf]
  rw [hind,integrable_indicator_iff (packingImage_open a ha).measurableSet]
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun t ht => (packingCoordinate_hasDerivAt a ha ht).hasDerivWithinAt)
    (packingCoordinate_strictMono a ha).injOn (fun x => f (packedDensity a ha x))
  apply h.trans
  apply integrableOn_congr_fun _ measurableSet_Ioo
  intro t ht
  dsimp only
  rw [packedDensity_coordinate a ha ht,abs_of_pos (one_div_pos.mpr (physicalProfile_pos a ha ht)),smul_eq_mul]

/-- The whole-line integral of a zero-preserving function of the actual packed density is exactly its original profile integral with the genuine reciprocal-profile Jacobian.
Use: packedDensity_mass, packedDensity_root_mass and packedDensity_energy evaluate the source mass, root mass and energy in the literal original normalization.
Article: jacobi, Proposition 2.2.
Proof: the actual zero extension removes the complement of the coordinate image. The original coordinate is differentiable and injective, so the community Jacobian theorem applies; its positive derivative and the true inverse identity give the printed profile integrand. -/
theorem packed_composition_integral (a : ℝ) (ha : -1<a) (f : ℝ → ℝ) (hf : f 0=0) :
    (∫ x : ℝ,f (packedDensity a ha x))=
      ∫ t in Ioo (0:ℝ) 1,(1/physicalProfile a ha t)*f ((physicalProfile a ha t)^2) := by
  -- The same genuine Jacobian is used for the integral and the separately proved integrability equivalence.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := packingImage a ha) (fun x hx => by rw [packedDensity_zero_outside a ha hx,hf])]
  rw [show packingImage a ha=packingCoordinate a ha '' Ioo (0:ℝ) 1 from rfl,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun t ht => (packingCoordinate_hasDerivAt a ha ht).hasDerivWithinAt)
      (packingCoordinate_strictMono a ha).injOn]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [packedDensity_coordinate a ha ht,abs_of_pos (one_div_pos.mpr (physicalProfile_pos a ha ht)),smul_eq_mul]

end
end jacobi.Trichotomy

import jacobi.Trichotomy.PackingCoordinate
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.MonotoneContinuity

/-!
Article: jacobi, Proposition 2.2.
Strict increase provides a unique inverse on the genuine open image.
Its continuity and derivative follow from the interval order isomorphism
and the ordinary inverse derivative theorem. Outside that image the
real representative is zero, so the source density can be extended by zero.
Use: packingInverse uses its unique inverse, whose order continuity fixes the source packing construction independently of support endpoints.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- The actual intrinsic coordinate as the canonical order isomorphism from the open physical interval to its genuine image.
Use: packingInverse uses its unique inverse, whose order continuity fixes the source packing construction independently of support endpoints.
Article: jacobi, Proposition C.4.
-/
def packingIso (a : ℝ) (ha : -1<a) : Ioo (0:ℝ) 1 ≃o packingImage a ha :=
  (packingCoordinate_strictMono a ha).orderIso (packingCoordinate a ha) (Ioo (0:ℝ) 1)

/-- The canonical order isomorphism is the original intrinsic coordinate itself.
Use: packingCoordinate_inverse transfers the genuine inverse identity to ordinary real coordinates.
Article: jacobi, Proposition 2.2.
Proof: unfold the community order isomorphism associated to a strictly increasing function. -/
theorem packingIso_apply (a : ℝ) (ha : -1<a) (t : Ioo (0:ℝ) 1) :
    (packingIso a ha t:ℝ)=packingCoordinate a ha t := by
  rfl

/-- The actual original inverse intrinsic coordinate, with zero as its total real representative outside the genuine packing image.
Use: packedDensity squares the unchanged original profile in this genuine inverse coordinate and extends it by zero off the image.
Article: jacobi, Proposition C.4.
-/
def packingInverse (a : ℝ) (ha : -1<a) (x : ℝ) : ℝ := by
  classical
  exact if hx : x∈packingImage a ha then ((packingIso a ha).symm ⟨x,hx⟩:ℝ) else 0

/-- The actual inverse coordinate always lies in the original physical interior on its genuine coordinate domain.
Use: positivity, the inverse Jacobian and the packed-density substitution apply to this actual interior value.
Article: jacobi, Proposition C.4.
Proof: the inverse order isomorphism takes values in the source open interval. -/
theorem packingInverse_mem (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    packingInverse a ha x∈Ioo (0:ℝ) 1 := by
  simp only [packingInverse,dite_eq_left hx]
  exact ((packingIso a ha).symm ⟨x,hx⟩).property

/-- The original intrinsic coordinate evaluated at its actual inverse returns the genuine coordinate value.
Use: the inverse derivative and the source density live in precisely the original packing coordinate, without a reparametrization premise.
Article: jacobi, Proposition 2.2.
Proof: evaluate the canonical order-isomorphism inverse identity and use the exact original-coordinate formula. -/
theorem packingCoordinate_inverse (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    packingCoordinate a ha (packingInverse a ha x)=x := by
  have h := congrArg Subtype.val ((packingIso a ha).apply_symm_apply ⟨x,hx⟩)
  rw [packingIso_apply] at h
  simpa only [packingInverse,dite_eq_left hx] using h

/-- The actual inverse intrinsic coordinate returns each original physical interior point.
Use: packedDensity_coordinate and all actual profile-to-density integral substitutions use this exact inverse identity.
Article: jacobi, Proposition 2.2.
Proof: both the original point and the inverse point are physical interior points with the same genuine coordinate. Strict increase gives their equality. -/
theorem packingInverse_coordinate (a : ℝ) (ha : -1<a) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    packingInverse a ha (packingCoordinate a ha t)=t :=
  (packingCoordinate_strictMono a ha).injOn
    (packingInverse_mem a ha ⟨t,ht,rfl⟩) ht (packingCoordinate_inverse a ha ⟨t,ht,rfl⟩)

/-- The genuine inverse intrinsic coordinate is continuous on its entire actual coordinate interval.
Use: packingInverse_hasDerivAt and measurability of the packed source density require the actual inverse, including both support regimes.
Article: jacobi, Proposition C.4.
Proof: the coordinate image is an interval, so its subspace topology equals its order topology. The inverse order isomorphism is continuous; its real representative agrees with that map on the image. -/
theorem packingInverse_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (packingInverse a ha) (packingImage a ha) := by
  have : OrdConnected (packingImage a ha) := packingImage_ordConnected a ha
  have hc : Continuous (fun x : packingImage a ha => ((packingIso a ha).symm x:ℝ)) :=
    continuous_subtype_val.comp (packingIso a ha).symm.continuous
  rw [continuousOn_iff_continuous_domRestrict]
  convert hc using 1
  ext x
  simp only [Set.domRestrict_apply,packingInverse,dite_eq_left x.property]

/-- The original inverse packing coordinate has the actual positive profile as derivative everywhere on its genuine open domain.
Use: the density identities and tail transfers use precisely dt/dx=phi_alpha(t), with the original centered normalization.
Article: jacobi, Proposition C.4.
Proof: the genuine inverse is continuous and the original coordinate has nonzero reciprocal-profile derivative. Its actual local inverse identity holds on the open packing image, so the ordinary inverse derivative theorem applies. -/
theorem packingInverse_hasDerivAt (a : ℝ) (ha : -1<a) {x : ℝ} (hx : x∈packingImage a ha) :
    HasDerivAt (packingInverse a ha) (physicalProfile a ha (packingInverse a ha x)) x := by
  have hm := packingInverse_mem a ha hx
  have h := HasDerivAt.of_local_left_inverse
    ((packingInverse_continuousOn a ha).continuousAt ((packingImage_open a ha).mem_nhds hx))
    (packingCoordinate_hasDerivAt a ha hm)
    (one_div_ne_zero (physicalProfile_pos a ha hm).ne') (by
      filter_upwards [(packingImage_open a ha).mem_nhds hx] with y hy
      exact packingCoordinate_inverse a ha hy)
  simpa only [one_div,inv_inv] using h

end
end jacobi.Trichotomy

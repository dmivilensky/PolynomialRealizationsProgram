import jacobi.Trichotomy.PackedDensity
import jacobi.Comparison.YoungProfile

/-!
Article: jacobi, Proposition C.4.
The genuine intrinsic coordinate constructed from phi_(1/2) is exactly
the inverse of the earlier Young hyperbolic coordinate. Consequently
the source density defined by the general packing construction is
literally (1/4)*sech(x)^4, with the same centered normalization.
Use: Young_packedDensity identifies the density from the general source construction with the literal original Young extremal.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The actual source packing coordinate and the earlier genuine Young intrinsic coordinate are exact inverses with the same center.
Use: Young_packedDensity identifies the density from the general source construction with the literal original Young extremal.
Article: jacobi, Proposition C.4.
Proof: the actual coordinate derivative is the reciprocal profile and the genuine Young intrinsic derivative is the same profile. Their composition has derivative one, hence its difference from x is constant; both centers equal zero. -/
theorem Young_coordinate_identity (ha : -1<(1/2:ℝ)) (x : ℝ) :
    packingCoordinate (1/2) ha (intrinsic x)=x := by
  -- The derivative calculation uses the genuine original profile, not an independently chosen ODE solution.
  have hder (y : ℝ) : HasDerivAt (fun y : ℝ => packingCoordinate (1/2) ha (intrinsic y)-y) 0 y := by
    have hp := physicalProfile_pos (1/2) ha (intrinsic_mem y)
    have h := ((packingCoordinate_hasDerivAt (1/2) ha (intrinsic_mem y)).comp y
      (jacobi.Comparison.U_packing_coordinate ha y)).sub (hasDerivAt_id y)
    rw [physicalProfile_eq (1/2) ha ⟨(intrinsic_mem y).1.le,(intrinsic_mem y).2.le⟩] at hp h
    convert h using 1
    · rfl
    · field_simp [hp.ne']
      ring
  have h := is_const_of_deriv_eq_zero (fun y => (hder y).differentiableAt)
    (fun y => (hder y).deriv) x 0
  have hz : intrinsic 0=(1/2:ℝ) := by simp [intrinsic]
  rw [hz,packingCoordinate_midpoint,sub_zero] at h
  linarith

/-- The actual inverse packing coordinate at the distinguished order is exactly the earlier original hyperbolic intrinsic coordinate.
Use: Young_packedDensity evaluates the general source density at every real spatial point.
Article: jacobi, Proposition C.4.
Proof: the genuine original coordinate takes the hyperbolic intrinsic point to x; apply its independently proved actual inverse identity. -/
theorem Young_inverse_identity (ha : -1<(1/2:ℝ)) (x : ℝ) :
    packingInverse (1/2) ha x=intrinsic x := by
  have h := packingInverse_coordinate (1/2) ha (intrinsic_mem x)
  rwa [Young_coordinate_identity] at h

/-- The density from the general original persymmetric packing construction is exactly the distinguished Young extremal at every real spatial point.
Use: completes the literal centered density equality in Proposition C.4, in the same packing definition used for every original order and all three tail regimes.
Article: jacobi, Proposition C.4.
Proof: the actual coordinate identity puts every x in the genuine image. Its true inverse is the original Young intrinsic point, and the independently proved original squared-profile formula there is exactly the distinguished density. -/
theorem Young_packedDensity (ha : -1<(1/2:ℝ)) (x : ℝ) :
    packedDensity (1/2) ha x=distinguished x := by
  have hx : x∈packingImage (1/2) ha :=
    ⟨intrinsic x,intrinsic_mem x,Young_coordinate_identity ha x⟩
  rw [packedDensity_on_image (1/2) ha hx,Young_inverse_identity,
    physicalProfile_eq (1/2) ha ⟨(intrinsic_mem x).1.le,(intrinsic_mem x).2.le⟩]
  exact jacobi.Comparison.U_packed_profile ha x

end
end jacobi.Trichotomy

import jacobi.Comparison.MainBounds
import jacobi.Young.IntrinsicCoordinate

/-!
Article: jacobi, Proposition C.4.
At U the actual limiting persymmetric profile gives precisely the
already constructed Young extremal in the original intrinsic packing
coordinate. The same genuine coordinate has the required derivative,
range, inverse and centered normalization; no new density is substituted.
Use: U_packed_profile identifies the limiting packed density in Theorem 4.1; U_packing_coordinate verifies the same original differential coordinate.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set jacobi.Reference jacobi.GelfandLevitan jacobi.Young

/-- The actual U persymmetric profile at the original Young intrinsic
coordinate equals the square root of the genuine original Young density.
Use: U_packed_profile identifies the limiting packed density in Theorem 4.1;
U_packing_coordinate verifies the same original differential coordinate.
Article: jacobi, Proposition C.4.
Proof: the actual original profile is 2*t*(1-t). Insert the already
constructed intrinsic t=(1+tanh(x))/2 and its exact hyperbolic identity. -/
theorem U_profile_intrinsic (ha:-1<(1/2:ℝ)) (x:ℝ) :
    persymmetricProfile (1/2) ha
      ⟨intrinsic x,⟨(intrinsic_mem x).1.le,(intrinsic_mem x).2.le⟩⟩=sqrt (distinguished x) := by
  rw [half_sine_persymmetricProfile,distinguished_sqrt]
  dsimp only [intrinsic]
  nlinarith [sech_sq x]

/-- The same genuine intrinsic Young coordinate obeys the original
packing-coordinate differential equation for the actual U profile.
Use: U_packed_profile is the density in the actual source packing
coordinate, not merely an algebraically matching change of variables.
Article: jacobi, Proposition C.4.
Proof: the independently proved actual intrinsic derivative is sqrt(m_U),
which the actual original persymmetric-profile identity identifies. -/
theorem U_packing_coordinate (ha:-1<(1/2:ℝ)) (x:ℝ) :
    HasDerivAt intrinsic (persymmetricProfile (1/2) ha
      ⟨intrinsic x,⟨(intrinsic_mem x).1.le,(intrinsic_mem x).2.le⟩⟩) x := by
  rw [U_profile_intrinsic,distinguished_sqrt]
  exact intrinsic_derivative x

/-- The actual U limiting packed persymmetric density is exactly the
original attained Young extremal, in its original centered intrinsic coordinate.
Use: this completes the profile identification in Theorem 4.1; the
same original range, endpoint limits and inverse are already proved
by intrinsic_mem, intrinsic_atBot, intrinsic_atTop and intrinsic_artanh.
Article: jacobi, Proposition C.4.
Proof: the source packed density is the square of the actual profile
at the genuine packing coordinate. The proved profile is sqrt(m_U),
and the actual nonnegative Young density selects its positive branch. -/
theorem U_packed_profile (ha:-1<(1/2:ℝ)) (x:ℝ) :
    (persymmetricProfile (1/2) ha
      ⟨intrinsic x,⟨(intrinsic_mem x).1.le,(intrinsic_mem x).2.le⟩⟩)^2=distinguished x := by
  rw [U_profile_intrinsic,sq_sqrt]
  unfold distinguished
  positivity

end
end jacobi.Comparison

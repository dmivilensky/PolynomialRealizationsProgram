import jacobi.GelfandLevitan.MidpointDirichlet

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
After the proved exact Dirichlet assignment, the other actual boundary
class has a real Robin parameter fixed by its genuine first midpoint
state. The original characteristic identity is normalized exactly as
2*a*(b-lambda*a)=kappa*Delta_sigma. The remaining Neumann assertion is
the substantive claim lambda=0; it is not assumed in these statements.
Use: midpointRobinCharacteristic describes its exact complex zero set before the remaining Neumann identification proves this genuine parameter zero.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual real separated boundary parameter of the original zero-based even target spectral class.
Use: midpointRobinCharacteristic describes its exact complex zero set before the remaining Neumann identification proves this genuine parameter zero.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def midpointRobinParameter (a : ℝ) (ha : -1<a) : ℂ :=
  midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)/
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)

/-- The genuine original non-Dirichlet boundary parameter is real.
Use: the final Neumann identification concerns a true real separated boundary condition of the original transformed equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: both original first midpoint coordinates are actual real-energy values and hence real complex inclusions. Their same genuine quotient is real. -/
theorem midpointRobinParameter_real (a : ℝ) (ha : -1<a) :
    ((midpointRobinParameter a ha).re:ℂ)=midpointRobinParameter a ha := by
  rw [midpointRobinParameter,midpointSlope_real,midpointValue_real,← Complex.ofReal_div]
  rfl

/-- The actual original Robin derivative characteristic, retaining the genuine boundary parameter rather than assuming it vanishes.
Use: midpointRobinCharacteristic_zero_iff and midpoint_robin_product provide exact spectral and normalization statements before the final Neumann step.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def midpointRobinCharacteristic (a : ℝ) (ha : -1<a) (z : ℂ) : ℂ :=
  midpointSlope a ha z-midpointRobinParameter a ha*midpointValue a ha z

/-- The original non-Dirichlet separated characteristic is exactly minus its nonzero first midpoint value times the actual Robin characteristic.
Use: midpointRobinCharacteristic_zero_iff transfers the proved exhaustive separated zero set to the genuine b-lambda*a function.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the first actual value is independently proved nonzero, so its true boundary quotient cancels exactly in the original determinant. -/
theorem separatedCharacteristic_robin (a : ℝ) (ha : -1<a) (z : ℂ) :
    separatedCharacteristic a ha 0 z=
      -midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)*
        midpointRobinCharacteristic a ha z := by
  unfold separatedCharacteristic midpointRobinCharacteristic midpointRobinParameter
  field_simp [midpoint_neumann_first_value_ne_zero a ha]
  ring

/-- The complete complex zeros of the genuine original Robin characteristic are exactly the original odd one-based target spectral class.
Use: the final Neumann identification needs only to prove the already determined actual parameter zero; no further spectral completeness premise remains.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: remove the fixed genuine nonzero first midpoint value from the original separated characteristic and use its independently proved full complex zero set. -/
theorem midpointRobinCharacteristic_zero_iff (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointRobinCharacteristic a ha z=0 ↔
      ∃ k:ℕ,z=(jacobi.Bessel.sigma a ha (parityIndex 0 k):ℂ) := by
  rw [← separatedCharacteristic_zero_iff a ha 0 z,separatedCharacteristic_robin,
    mul_eq_zero,or_iff_right (neg_ne_zero.mpr (midpoint_neumann_first_value_ne_zero a ha))]

/-- The genuine original Robin characteristic has leading normalization one relative to y*a_0 on the shifted negative axis.
Use: midpoint_robin_product determines the exact printed kappa scalar of the actual characteristic product.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the original b/(y*a_0) tends to one and the original a/(y*a_0) tends to zero. The actual fixed boundary parameter therefore contributes only a vanishing lower-order term. -/
theorem midpointRobinCharacteristic_negative_leading (a : ℝ) (ha : -1<a) :
    Tendsto (fun y:ℝ => midpointRobinCharacteristic a ha (shiftedNegativeEnergy a y)/
      ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))) atTop (𝓝 1) := by
  have h := (midpointSlope_negative_leading a ha).sub
    ((midpointValue_negative_scaled a ha).const_mul (midpointRobinParameter a ha))
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [] with y
  dsimp only [midpointRobinCharacteristic,shiftedNegativeEnergy]
  ring

/-- The original midpoint value and genuine Robin characteristic have the exact full Bessel characteristic product with the printed scalar kappa.
Use: after the remaining actual boundary parameter is proved zero, this is precisely the full 2*a*b=kappa*Delta_sigma assertion of Proposition C.2.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: remove the actual nonzero first value and first Dirichlet slope from the independently proved full separated-product factorization. Divide the remaining product by y*a_0^2 on the negative axis. Both original wave factors tend to one in their reference normalization, whereas Delta_sigma has the proved exact limit 2/kappa. Uniqueness of limits fixes the scalar, with no boundary parameter premise supplied. -/
theorem midpoint_robin_product (a : ℝ) (ha : -1<a) (z : ℂ) :
    2*midpointValue a ha z*midpointRobinCharacteristic a ha z=
      ((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicSigma a z := by
  -- First retain the genuine original boundary coefficients in the established full separated-product identity.
  let A := midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)
  let B := midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex 1 0):ℂ)
  let M := -(A*B)
  let κ : ℂ := ((2*Real.pi^2*normConstant a:ℝ):ℂ)
  have hk : κ≠0 := Complex.ofReal_ne_zero.mpr (by positivity [normConstant_pos ha])
  have hA : A≠0 := midpoint_neumann_first_value_ne_zero a ha
  have hB : B≠0 := (midpoint_spectral_state_nonzero a ha 1 0).resolve_left
    (not_not.mpr (midpoint_dirichlet_first a ha))
  have hM : M≠0 := neg_ne_zero.mpr (mul_ne_zero hA hB)
  obtain ⟨C,_,hfactor⟩ := separatedProduct_factorization a ha
  have hprod (w : ℂ) : midpointValue a ha w*midpointRobinCharacteristic a ha w=
      (C/M)*characteristicSigma a w := by
    apply mul_left_cancel₀ hM
    have h := hfactor w
    rw [separatedCharacteristic_robin,separatedCharacteristic_dirichlet] at h
    change (-A*midpointRobinCharacteristic a ha w)*(midpointValue a ha w*B)=C*characteristicSigma a w at h
    calc
      _ = (-A*midpointRobinCharacteristic a ha w)*(midpointValue a ha w*B) := by dsimp [M]; ring
      _ = C*characteristicSigma a w := h
      _ = _ := by field_simp [hM]
  -- The same actual negative-axis normalizations determine the remaining scalar exactly.
  have hL := (transformed_midpoint_negative_limit a ha).mul
    (midpointRobinCharacteristic_negative_leading a ha)
  simp only [mul_one] at hL
  have hR := (characteristicSigma_negative_reference_limit a ha).const_mul (C/M)
  have he : (fun y:ℝ => (midpointValue a ha (shiftedNegativeEnergy a y)/
      solution a (shiftedNegativeEnergy a y) (1/2))*
      (midpointRobinCharacteristic a ha (shiftedNegativeEnergy a y)/
        ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))))=
      (fun y => (C/M)*(characteristicSigma a (shiftedNegativeEnergy a y)/
        ((y:ℂ)*(solution a (shiftedNegativeEnergy a y) (1/2))^2))) := by
    funext y
    rw [div_mul_div_comm,hprod]
    ring
  change Tendsto (fun y:ℝ => (midpointValue a ha (shiftedNegativeEnergy a y)/
    solution a (shiftedNegativeEnergy a y) (1/2))*
    (midpointRobinCharacteristic a ha (shiftedNegativeEnergy a y)/
    ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2)))) atTop (𝓝 1) at hL
  rw [he] at hL
  have hl := tendsto_nhds_unique hL hR
  have hscale : 2*(C/M)=κ := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hM).mpr
    change 1=(C/M)*(2/κ) at hl
    field_simp [hk] at hl
    linear_combination -hl
  calc
    _ = 2*(midpointValue a ha z*midpointRobinCharacteristic a ha z) := by ring
    _ = 2*((C/M)*characteristicSigma a z) := by rw [hprod]
    _ = κ*characteristicSigma a z := by rw [← mul_assoc,hscale]

end
end jacobi.GelfandLevitan

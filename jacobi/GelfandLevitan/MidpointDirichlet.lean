import jacobi.GelfandLevitan.SeparatedNegative
import jacobi.Reference.NormingSigns

/-!
Article: jacobi, Proposition C.2.
The genuine Dirichlet class is exactly the article's even one-based
indices. The opposite assignment contradicts the original signed
norming formula and the positive actual transformed-wave norm. Thus
a has exactly the prescribed Dirichlet zeros, all simple, without
assuming either boundary class in the construction.
Use: midpoint_dirichlet_first identifies the true Dirichlet class as the opposite, zero-based odd class.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual first midpoint value in the zero-based even class is nonzero.
Use: midpoint_dirichlet_first identifies the true Dirichlet class as the opposite, zero-based odd class.
Article: jacobi, Proposition C.2.
Proof: if that value vanished, the genuine separated product on the negative axis would force J=C*2/kappa, where J is the nonzero other-class boundary determinant at sigma_0. Differentiate the proved original product at sigma_0; its genuine Green derivative is the positive squared half norm. Cancellation gives kappa*Delta_sigma'=2*norm^2>0, contradicting the original signed positive norming weight at index zero. -/
theorem midpoint_neumann_first_value_ne_zero (a : ℝ) (ha : -1<a) :
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 0 0):ℂ)≠0 := by
  -- The signed original norming data, rather than a convention about parity names, selects the actual Dirichlet class.
  intro hA
  let E := jacobi.Bessel.sigma a ha (parityIndex 0 0)
  let B := midpointSlope a ha (E:ℂ)
  let J := separatedCharacteristic a ha 1 (E:ℂ)
  let κ : ℂ := ((2*Real.pi^2*normConstant a:ℝ):ℂ)
  let n := inner ℝ (transformedVector a ha E) (transformedVector a ha E)
  have hk : κ≠0 := Complex.ofReal_ne_zero.mpr (by positivity [normConstant_pos ha])
  obtain ⟨C,hC,hfactor⟩ := separatedProduct_factorization a ha
  have h0 := separatedCharacteristic_at_spectrum a ha 0 0
  have hS0 : Tendsto (fun y:ℝ => separatedCharacteristic a ha 0 (shiftedNegativeEnergy a y)/
      solution a (shiftedNegativeEnergy a y) (1/2)) atTop (𝓝 B) := by
    have h := (transformed_midpoint_negative_limit a ha).mul_const B
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [] with y
    change (midpointValue a ha (shiftedNegativeEnergy a y)/solution a (shiftedNegativeEnergy a y) (1/2))*B=_
    rw [separatedCharacteristic,hA,mul_zero,sub_zero]
    ring
  have hL := hS0.mul (separatedCharacteristic_negative_leading a ha 1)
  have hR := (characteristicSigma_negative_reference_limit a ha).const_mul C
  have he : (fun y:ℝ => (separatedCharacteristic a ha 0 (shiftedNegativeEnergy a y)/
      solution a (shiftedNegativeEnergy a y) (1/2))*
      (separatedCharacteristic a ha 1 (shiftedNegativeEnergy a y)/
        ((y:ℂ)*solution a (shiftedNegativeEnergy a y) (1/2))))=
      (fun y => C*(characteristicSigma a (shiftedNegativeEnergy a y)/
        ((y:ℂ)*(solution a (shiftedNegativeEnergy a y) (1/2))^2))) := by
    funext y
    rw [div_mul_div_comm,hfactor]
    ring
  rw [he] at hL
  have hlimit := tendsto_nhds_unique hL hR
  have hJvalue : J=B*(-midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 1 0):ℂ)) := by
    dsimp [J,separatedCharacteristic,E,B]
    rw [hA,zero_mul,zero_sub]
    ring
  have hJC : J=C*(2/κ) := hJvalue.trans hlimit
  -- Differentiate the actual full product at the same original first spectral point.
  have hS0d : deriv (separatedCharacteristic a ha 0) (E:ℂ)=(n:ℂ) := by
    rw [separatedCharacteristic_derivative]
    exact midpoint_green_derivative a ha E
  have hleft := ((separatedCharacteristic_analytic a ha 0 (E:ℂ)).differentiableAt.hasDerivAt.mul
    (separatedCharacteristic_analytic a ha 1 (E:ℂ)).differentiableAt.hasDerivAt)
  have hright := (characteristicSigma_analytic a (E:ℂ)).differentiableAt.hasDerivAt.const_mul C
  have hfun : (fun z => separatedCharacteristic a ha 0 z*separatedCharacteristic a ha 1 z)=
      (fun z => C*characteristicSigma a z) := funext hfactor
  change HasDerivAt (fun z => separatedCharacteristic a ha 0 z*separatedCharacteristic a ha 1 z) _ (E:ℂ) at hleft
  rw [hfun] at hleft
  have hd := hleft.unique hright
  rw [hS0d,h0,zero_mul,add_zero] at hd
  change (n:ℂ)*J=C*deriv (characteristicSigma a) (E:ℂ) at hd
  rw [hJC] at hd
  field_simp [hk] at hd
  have hN : 2*(n:ℂ)=κ*deriv (characteristicSigma a) (E:ℂ) := by
    linear_combination hd
  -- The original positive norming weight at index zero has the opposite derivative sign.
  have hD := characteristicSigma_simple ha ((characteristicSigma_zero_iff ha (E:ℂ)).mpr ⟨0,rfl⟩)
  have hW := norming_signed_bessel ha 0
  norm_num only [zero_add,pow_one] at hW
  change ((normingRatio a ha 0/norming a 0:ℝ):ℂ)= -1/(κ*deriv (characteristicSigma a) (E:ℂ)) at hW
  rw [eq_div_iff (mul_ne_zero hk hD),← hN] at hW
  have hn : 0<n := transformedVector_spectral_norm_pos a ha 0 0
  have hw : 0<normingRatio a ha 0/norming a 0 :=
    div_pos (normingRatio_properties ha 0).2 (norming_pos ha 0)
  have hr : (normingRatio a ha 0/norming a 0)*(2*n)= -1 := by exact_mod_cast hW
  nlinarith

/-- The first original zero-based odd spectral state has actual Dirichlet midpoint value zero.
Use: midpointValue_zero_iff identifies the complete actual Dirichlet zero set and its genuine simple zeros.
Article: jacobi, Proposition C.2.
Proof: the proved negative-axis product argument forces one first class value to vanish; the original signed norming argument excludes the opposite class. -/
theorem midpoint_dirichlet_first (a : ℝ) (ha : -1<a) :
    midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex 1 0):ℂ)=0 :=
  (midpoint_first_values_product_zero a ha).resolve_left (midpoint_neumann_first_value_ne_zero a ha)

/-- The original Dirichlet separated characteristic is exactly its nonzero first slope times the original midpoint value characteristic.
Use: midpointValue_zero_iff and midpointValue_simple transfer the independently proved full complex separated zero set and its multiplicities to the actual a.
Article: jacobi, Proposition C.2.
Proof: the first original Dirichlet value vanishes, so the unchanged actual two-term separated determinant reduces to its genuine first slope coefficient times a. -/
theorem separatedCharacteristic_dirichlet (a : ℝ) (ha : -1<a) (z : ℂ) :
    separatedCharacteristic a ha 1 z=midpointValue a ha z*
      midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex 1 0):ℂ) := by
  rw [separatedCharacteristic,midpoint_dirichlet_first,mul_zero,sub_zero]

/-- The full complex zeros of the actual original midpoint value characteristic are exactly the original even one-based target spectral class.
Use: the full reflected target differential realization has its genuine Dirichlet midpoint data on precisely the required odd reflection class.
Article: jacobi, Proposition C.2.
Proof: its genuine Dirichlet separated characteristic is a fixed nonzero slope multiple, and its exhaustive complex zero set was independently proved from the actual transformed Hilbert basis. -/
theorem midpointValue_zero_iff (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointValue a ha z=0 ↔ ∃ k:ℕ,z=(jacobi.Bessel.sigma a ha (parityIndex 1 k):ℂ) := by
  have hB := (midpoint_spectral_state_nonzero a ha 1 0).resolve_left
    (not_not.mpr (midpoint_dirichlet_first a ha))
  rw [← separatedCharacteristic_zero_iff a ha 1 z,separatedCharacteristic_dirichlet,
    mul_eq_zero,or_iff_left hB]

/-- Every complex zero of the actual original Dirichlet midpoint characteristic is simple in energy.
Use: the reflected original Dirichlet eigenfunctions and the exact target characteristic product retain the required genuine spectral multiplicity one.
Article: jacobi, Proposition C.2.
Proof: its entire separated characteristic has the same zeros and is a fixed original scalar multiple of a. A vanishing derivative of a would therefore give a multiple zero of that independently proved simple characteristic. -/
theorem midpointValue_simple (a : ℝ) (ha : -1<a) {z : ℂ} (hz : midpointValue a ha z=0) :
    deriv (midpointValue a ha) z≠0 := by
  have hS : separatedCharacteristic a ha 1 z=0 := by rw [separatedCharacteristic_dirichlet,hz,zero_mul]
  have hd := separatedCharacteristic_simple a ha 1 hS
  rw [separatedCharacteristic_derivative,midpoint_dirichlet_first,mul_zero,sub_zero] at hd
  exact fun h => hd (by rw [h,zero_mul])

end
end jacobi.GelfandLevitan

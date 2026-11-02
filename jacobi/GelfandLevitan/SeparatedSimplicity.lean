import jacobi.GelfandLevitan.SeparatedCharacteristics

/-!
Article: jacobi, Proposition C.2.
Every zero of either actual separated characteristic is simple in the
original complex energy. The determinant derivative equals a strictly
positive genuine transformed-wave norm. No eigenvalue simplicity or
characteristic derivative is assumed as an additional input.
Use: separatedCharacteristic_simple turns the original differentiated Green identity into a nonzero characteristic derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Every genuine original transformed spectral vector has strictly positive squared Hilbert norm.
Use: separatedCharacteristic_simple turns the original differentiated Green identity into a nonzero characteristic derivative.
Article: jacobi, Proposition C.2.
Proof: its independently proved normalized basis entry has squared norm one. A zero unnormalized vector would make that same entry zero, contradicting its actual orthonormality. -/
theorem transformedVector_spectral_norm_pos (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    0 < inner ℝ (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k)))
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k))) := by
  apply real_inner_self_pos.mpr
  intro hz
  have h := normalizedTransformedVector_parity_inner a ha p k k
  rw [normalizedTransformedVector,hz,smul_zero,inner_zero_left] at h
  norm_num at h

/-- The derivative of the original separated characteristic is the genuine energy derivative of its two actual midpoint coordinates with the original fixed boundary coefficients.
Use: separatedCharacteristic_simple relates a hypothetical double zero to the true Green determinant derivative.
Article: jacobi, Proposition C.2.
Proof: differentiate the actual entire value and slope characteristics, keeping their original first spectral boundary state fixed. -/
theorem separatedCharacteristic_derivative (a : ℝ) (ha : -1<a) (p : Fin 2) (z : ℂ) :
    deriv (separatedCharacteristic a ha p) z=
      deriv (midpointValue a ha) z*midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)-
        deriv (midpointSlope a ha) z*midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ) :=
  (((midpointValue_analytic a ha z).differentiableAt.hasDerivAt.mul_const _).sub
    ((midpointSlope_analytic a ha z).differentiableAt.hasDerivAt.mul_const _)).deriv

/-- Every zero of either actual original separated characteristic is simple in the original complex energy variable.
Use: the exact Neumann/Dirichlet classification and characteristic product of general Proposition C.2 use both exhaustive original parity zero sets with their proved multiplicity one.
Article: jacobi, Proposition C.2.
Proof: the exhaustive zero-set theorem puts the alleged multiple zero at a genuine original spectral point. If its separated derivative vanished, the derivative state would satisfy the same boundary condition as that spectral state. Their determinant would vanish. The independently differentiated actual Green identity instead identifies it with the strictly positive genuine half-interval norm. -/
theorem separatedCharacteristic_simple (a : ℝ) (ha : -1<a) (p : Fin 2) {z : ℂ}
    (hz : separatedCharacteristic a ha p z=0) : deriv (separatedCharacteristic a ha p) z≠0 := by
  -- Positivity is supplied by the already proved actual transformed basis; it is not a characteristic normalization premise.
  obtain ⟨k,rfl⟩ := (separatedCharacteristic_zero_iff a ha p z).mp hz
  intro hd
  rw [separatedCharacteristic_derivative] at hd
  have hdet := separated_determinant_zero (midpoint_spectral_state_nonzero a ha p 0)
    hd (separatedCharacteristic_at_spectrum a ha p k)
  rw [midpoint_green_derivative] at hdet
  have hn := transformedVector_spectral_norm_pos a ha p k
  exact hn.ne' (Complex.ofReal_injective hdet)

end
end jacobi.GelfandLevitan

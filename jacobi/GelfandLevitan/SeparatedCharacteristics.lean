import jacobi.GelfandLevitan.ComplexHilbertGreen
import jacobi.GelfandLevitan.MidpointBoundaryStates
import jacobi.GelfandLevitan.Triangle

/-!
Article: jacobi, Proposition C.2.
The genuine first midpoint state of each original parity class fixes
its separated characteristic, with no angle choice or boundary premise.
Its complex zeros are exactly the prescribed sigma values of that class.
The proof uses the actual Green identity, the two actual transformed
bases, and the selected endpoint normalization of the original u.
Use: its complete simple zero set is the spectral input for the exact Neumann/Dirichlet classification and product identity of Proposition C.2.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The separated midpoint characteristic determined by the actual first nonzero spectral state of the chosen parity.
Use: its complete simple zero set is the spectral input for the exact Neumann/Dirichlet classification and product identity of Proposition C.2.
Article: jacobi, Proposition C.2.
-/
def separatedCharacteristic (a : ℝ) (ha : -1<a) (p : Fin 2) (z : ℂ) : ℂ :=
  midpointValue a ha z*midpointSlope a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)-
    midpointSlope a ha z*midpointValue a ha (jacobi.Bessel.sigma a ha (parityIndex p 0):ℂ)

/-- The actual separated characteristic is entire in the original complex energy.
Use: separatedCharacteristic_simple differentiates this same genuine function at each of its spectral zeros.
Article: jacobi, Proposition C.2.
Proof: both actual midpoint characteristics are entire and the original boundary coefficients are fixed scalars. -/
theorem separatedCharacteristic_analytic (a : ℝ) (ha : -1<a) (p : Fin 2) (z : ℂ) :
    AnalyticAt ℂ (separatedCharacteristic a ha p) z :=
  ((midpointValue_analytic a ha z).mul analyticAt_const).sub
    ((midpointSlope_analytic a ha z).mul analyticAt_const)

/-- Every original prescribed energy of a parity class is a zero of its actual separated characteristic.
Use: separatedCharacteristic_zero_iff proves both directions of the full original complex zero-set identification.
Article: jacobi, Proposition C.2.
Proof: the actual same-parity midpoint states are collinear by the proved original Hilbert Green identity and orthogonality. -/
theorem separatedCharacteristic_at_spectrum (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    separatedCharacteristic a ha p (jacobi.Bessel.sigma a ha (parityIndex p k):ℂ)=0 :=
  midpoint_parity_collinear a ha p k 0

/-- Two states satisfying the same nontrivial separated boundary condition have zero determinant.
Use: separatedCharacteristic_zero_iff applies the actual Green identity between any alleged additional zero and every genuine spectral state of the same class.
Article: jacobi, Proposition C.2.
Source: elementary two-dimensional determinant algebra.
Proof: multiply the desired determinant by each nonzero boundary coefficient and express it as a linear combination of the two vanished original boundary determinants. -/
theorem separated_determinant_zero {A B x y v w : ℂ} (h : A≠0 ∨ B≠0)
    (hx : x*B-y*A=0) (hv : v*B-w*A=0) : x*w-y*v=0 := by
  rcases h with hA|hB
  · apply (mul_eq_zero.mp (show A*(x*w-y*v)=0 by
      linear_combination v*hx-x*hv)).resolve_left hA
  · apply (mul_eq_zero.mp (show B*(x*w-y*v)=0 by
      linear_combination w*hx-y*hv)).resolve_left hB

/-- The complete complex zero set of each actual separated midpoint characteristic is exactly the original target spectrum of that parity class.
Use: the subsequent Neumann/Dirichlet identification and exact characteristic factorization require an exhaustive zero set, including exclusion of nonreal and additional real zeros.
Article: jacobi, Proposition C.2.
Proof: an additional zero has zero boundary determinant with every original spectral state of the class. Its actual Green pairings therefore vanish. The independently proved complete transformed basis annihilates both real and imaginary parts of the same original u. Continuity makes u pointwise zero, contradicting its independently proved selected endpoint branch. -/
theorem separatedCharacteristic_zero_iff (a : ℝ) (ha : -1<a) (p : Fin 2) (z : ℂ) :
    separatedCharacteristic a ha p z=0 ↔
      ∃ k:ℕ,z=(jacobi.Bessel.sigma a ha (parityIndex p k):ℂ) := by
  -- Completeness is used on the actual original function, with its complex-to-real pairing bridge proved independently.
  constructor
  · intro hz
    by_contra h
    push Not at h
    have hpair (k : ℕ) : coefficientFunctional
        (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k)):Space)
          (transformedWaveMap a ha z)=0 := by
      have hd := separated_determinant_zero (midpoint_spectral_state_nonzero a ha p 0)
        hz (separatedCharacteristic_at_spectrum a ha p k)
      have hG := complex_hilbert_green a ha z (jacobi.Bessel.sigma a ha (parityIndex p k))
      rw [hd] at hG
      exact (mul_eq_zero.mp hG).resolve_left (sub_ne_zero.mpr (h k))
    obtain ⟨t,ht⟩ := transformedSolution_not_identically_zero a ha z
    have hz := half_complex_pairing_total a ha p (transformedWaveMap a ha z) hpair t
    rw [transformedWaveMap_apply,halfClamp_halfInclusion] at hz
    exact ht hz
  · rintro ⟨k,rfl⟩
    exact separatedCharacteristic_at_spectrum a ha p k

end
end jacobi.GelfandLevitan

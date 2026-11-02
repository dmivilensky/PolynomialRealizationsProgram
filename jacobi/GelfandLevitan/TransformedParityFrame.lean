import jacobi.GelfandLevitan.ParityPositiveForm
import jacobi.GelfandLevitan.TransformationInverse

/-!
Article: jacobi, Proposition C.2.
The actual transformed waves satisfy the complete printed tight-frame
identity in both physical parity classes. Completeness follows for
each family separately. Orthonormality additionally uses the compact
perturbation argument in the article's Basis paragraph.
Use: transformed_parity_parseval identifies the original positive source form with the genuine transformed frame coefficients.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Pairing the actual transformed wave is the original reference coefficient of the genuine adjoint-transformed input.
Use: transformed_parity_parseval identifies the original positive source form with the genuine transformed frame coefficients.
Article: jacobi, Proposition C.2.
Proof: the original transformation sends the actual reference coefficient vector to the actual transformed solution vector. Move that genuine bounded transformation through its true Hilbert adjoint and use the original coefficient-vector integral identity. -/
theorem transformedVector_inner (a : ℝ) (ha : -1<a) (E : ℝ) (v : halfSubspace) :
    inner ℝ (transformedVector a ha E) v=
      realCoefficient a ((transformationPlus a ha).adjoint v:Space) E := by
  rw [← transformationPlus_coefficientVector,← ContinuousLinearMap.adjoint_inner_right,
    coefficientVector_inner]

/-- The two actual transformed parity families satisfy the exact printed norming-weighted Parseval frame identity.
Use: proves each family's genuine completeness and feeds the invertible compact-perturbation argument for Two orthonormal bases.
Article: jacobi, Proposition C.2.
Proof: apply the proved original parity positive-form sum to the actual adjoint-transformed input. The independently proved exact GL factorization gives its original norm square, and the true transformed-wave pairing identifies every spectral coefficient. -/
theorem transformed_parity_parseval (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    HasSum (fun k => 2*normingRatio a ha (parityIndex p k)*
      (inner ℝ (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k))) v)^2/
        norming a (parityIndex p k)) (‖v‖^2) := by
  have h := parity_positive_hasSum a ha p ((transformationPlus a ha).adjoint v)
  rw [transformation_factorization_form] at h
  simpa only [transformedVector_inner] using h

/-- Each actual transformed parity family detects every original half-interval L2 input.
Use: supplies the true density premise in the compact-perturbation Basis argument and the midpoint boundary classification of Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: vanishing of all actual transformed coefficients makes the independently proved convergent frame sum zero, hence the true Hilbert norm is zero. -/
theorem transformed_parity_total (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace)
    (hz : ∀ k,inner ℝ (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p k))) v=0) :
    v=0 := by
  have h := transformed_parity_parseval a ha p v
  simp only [hz,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div] at h
  have hn : ‖v‖^2=0 := h.unique hasSum_zero
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end
end jacobi.GelfandLevitan

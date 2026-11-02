import jacobi.GelfandLevitan.HalfReferenceCompleteness
import jacobi.GelfandLevitan.CoefficientVectors

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
The two actual half-reference Hilbert bases have precisely the printed
norming-weighted source coefficient Parseval sums. All coefficients
remain the original spatial integrals on the original half domain.
Use: half_reference_parseval gives the literal source Parseval formula used to cancel the reference term in the parity GL form.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Each actual half-reference basis coefficient is its original physical integral with the printed normalization.
Use: half_reference_parseval gives the literal source Parseval formula used to cancel the reference term in the parity GL form.
Article: jacobi, Proposition C.2.
Proof: the actual half projection preserves pairing with the supported input. The complete full reference basis has its original norming normalization, and its integral equals the original half-supported source coefficient. -/
theorem halfReferenceVector_inner (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) (v : halfSubspace) :
    inner ℝ (halfReferenceVector a ha p k) v=
      (Real.sqrt 2/Real.sqrt (norming a (parityIndex p k)))*
        realCoefficient a (v:Space) (eigenvalue a (parityIndex p k)) := by
  rw [halfReferenceVector,real_inner_smul_left
    (halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p k))) v (Real.sqrt 2),
    halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,hilbertBasis_apply,normalizedWave,
    real_inner_smul_left,← referenceCoefficient_inner,
    ← realCoefficient_reference a (v:Space) (halfSubspace_supported v)]
  ring

/-- Each original parity class has the exact physical half-interval Parseval sum in genuine source integral coefficients.
Use: adding the actual parity GL correction gives parity_positive_hasSum, and then the transformed tight-frame identity.
Article: jacobi, Proposition C.2.
Proof: apply community Parseval to the independently proved complete original half-reference basis. Identify each coefficient with its actual spatial integral; the two genuine positive square-root normalizations square to 2/fn_k. -/
theorem half_reference_parseval (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    HasSum (fun k => 2*(realCoefficient a (v:Space) (eigenvalue a (parityIndex p k)))^2/
      norming a (parityIndex p k)) (‖v‖^2) := by
  -- Completeness of each original parity restriction has already been proved by physical extension.
  have h := (halfReferenceBasis a ha p).hasSum_inner_mul_inner v v
  rw [real_inner_self_eq_norm_sq] at h
  apply h.congr_fun
  intro k
  rw [halfReferenceBasis_apply,real_inner_comm (halfReferenceVector a ha p k) v,
    halfReferenceVector_inner]
  have hp := norming_pos ha (parityIndex p k)
  rw [← pow_two,mul_pow,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt hp.le]
  ring

end
end jacobi.GelfandLevitan

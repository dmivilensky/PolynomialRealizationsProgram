import jacobi.GelfandLevitan.HalfReferenceParseval
import jacobi.GelfandLevitan.KernelPairing
import jacobi.GelfandLevitan.ParityKernelMaps

/-!
Article: jacobi, Proposition C.2.
Each physical parity class represents the entire original positive
operator form. Both uniform parity summation and the complete original
half-reference Parseval identity are proved for the actual data.
Use: parity_positive_hasSum cancels the actual reference Parseval coefficients to obtain the original positive target form in each parity class.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The original parity correction coefficient series has the genuine full source kernel form as its sum.
Use: parity_positive_hasSum cancels the actual reference Parseval coefficients to obtain the original positive target form in each parity class.
Article: jacobi, Proposition C.2.
Proof: apply the proved bounded bilinear integral functional to the actual uniform parity kernel sum. Each original integral term is its independently proved norming-weighted coefficient correction. -/
theorem parity_kernel_quadratic_hasSum (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    HasSum (fun k => 2*((normingRatio a ha (parityIndex p k)*
      (realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha (parityIndex p k)))^2-
      (realCoefficient a (v:Space) (eigenvalue a (parityIndex p k)))^2)/
        norming a (parityIndex p k))) (kernelQuadratic a ha (v:Space)) := by
  -- The spatial integration is a bounded linear map of the actual uniform kernel, so the interchange is justified for every original L2 input.
  have hK := (parity_kernelTermMap_hasSum a ha p).const_smul (2:ℝ)
  have hscale : (2:ℝ) • ((1/2:ℝ) • kernelMap a ha)=kernelMap a ha := by
    rw [smul_smul]
    norm_num
  rw [hscale] at hK
  have h := (kernelPairing (v:Space) (v:Space)).hasSum hK
  change HasSum (fun k => kernelPairing (v:Space) (v:Space)
    ((2:ℝ) • kernelTermMap a ha (parityIndex p k))) (kernelQuadratic a ha (v:Space)) at h
  apply h.congr_fun
  intro k
  rw [map_smul,smul_eq_mul]
  change 2*((normingRatio a ha (parityIndex p k)*
    (realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha (parityIndex p k)))^2-
    (realCoefficient a (v:Space) (eigenvalue a (parityIndex p k)))^2)/
      norming a (parityIndex p k))=2*(∫ x:Interval×Interval,
        ((v:Space) x.1*(v:Space) x.2)*kernelTerm a ha (parityIndex p k)
          (halfTime x.1) (halfTime x.2) ∂(MeasureTheory.volume.prod MeasureTheory.volume))
  rw [kernelTerm_quadratic]

/-- Each genuine source parity spectral family represents exactly the entire original positive operator form.
Use: the proved GL factorization turns this true source form into the norm square of the actual transformed parity family.
Article: jacobi, Proposition C.2.
Proof: add the independently proved complete half-reference Parseval sum to the actual parity correction sum. Their true reference coefficients cancel term by term; the unchanged actual kernel form plus the original norm is the original positive operator form. -/
theorem parity_positive_hasSum (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    HasSum (fun k => 2*normingRatio a ha (parityIndex p k)*
      (realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha (parityIndex p k)))^2/
        norming a (parityIndex p k)) (inner ℝ (positiveOperator a ha v) v) := by
  -- Both convergent sums concern the same original coefficients and normalization.
  have h := (half_reference_parseval a ha p v).add (parity_kernel_quadratic_hasSum a ha p v)
  have hform : inner ℝ (positiveOperator a ha v) v=‖v‖^2+kernelQuadratic a ha (v:Space) := by
    change inner ℝ (v+kernelOperator a ha v) v=_
    rw [inner_add_left,real_inner_self_eq_norm_sq,kernelOperator_quadratic]
  rw [← hform] at h
  apply h.congr_fun
  intro k
  ring

end
end jacobi.GelfandLevitan

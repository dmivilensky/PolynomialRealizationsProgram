import jacobi.GelfandLevitan.MidpointDirichlet
import jacobi.GelfandLevitan.ParityKernelMaps
import jacobi.Reference.Midpoint

/-!
Article: jacobi, Proposition C.2.
The actual original diagonal satisfies w(1/2)=0. A direct uniformly
convergent parity-row argument replaces the fine negative-axis
comparison for this assertion: reference Dirichlet midpoint values
remove the unperturbed terms, and the genuine transformed Dirichlet
values annihilate every remaining row term under the original GL
midpoint functional.
Use: kernelDiagonal_midpoint_zero applies this same source transformation to the norm-convergent original Dirichlet parity kernel rows.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine original transformed midpoint evaluation as a real bounded functional on continuous source waves.
Use: kernelDiagonal_midpoint_zero applies this same source transformation to the norm-convergent original Dirichlet parity kernel rows.
Article: jacobi, Proposition C.2.
-/
def midpointRowEvaluation (a : ℝ) (ha : -1<a) : C(Interval,ℝ) →L[ℝ] ℝ :=
  ContinuousMap.evalCLM ℝ (halfInclusion halfMidpoint)+
    (innerSL ℝ (solutionRow a ha halfMidpoint)).comp rowEmbedding

/-- The actual real midpoint functional maps every original real source wave to its genuine transformed midpoint value.
Use: the original Dirichlet transformed values annihilate each genuine parity kernel row in kernelDiagonal_midpoint_zero.
Article: jacobi, Proposition C.2.
Proof: its genuine row embedding is the original coefficient vector. Move the real Hilbert pairing into the proved true source coefficient and use the actual original transformed-solution reality formula. -/
theorem midpointRowEvaluation_wave (a : ℝ) (ha : -1<a) (E : ℝ) :
    midpointRowEvaluation a ha (realHalfWave a ha E)=(midpointValue a ha (E:ℂ)).re := by
  change realSolution a E (min (1/2) (1/2))+
    inner ℝ (solutionRow a ha halfMidpoint) (coefficientVector a ha E)=_
  rw [min_self,real_inner_comm,coefficientVector_inner,midpointValue_real]
  rfl

/-- The actual bounded extraction of the original physical midpoint row of a continuous full source kernel.
Use: the genuine uniform Dirichlet parity kernel series is transformed into its actual continuous midpoint-row series before applying midpointRowEvaluation.
Article: jacobi, Proposition C.2.
-/
def midpointKernelRowCLM : C(Interval×Interval,ℝ) →L[ℝ] C(Interval,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ
    (⟨fun r:Interval => (halfInclusion halfMidpoint,r),continuous_const.prodMk continuous_id⟩ : C(Interval,Interval×Interval))

/-- Each genuine Dirichlet parity source kernel row at the midpoint contains only its original perturbed wave term.
Use: kernelDiagonal_midpoint_zero applies the original midpoint transformation termwise, where the genuine transformed Dirichlet value is zero.
Article: jacobi, Proposition C.2.
Proof: the actual reference Dirichlet value f(1/2,tau_(2*k+1)) is zero. The unchanged original kernel summand therefore reduces exactly to its norming weight times f(1/2,sigma_k)*f(.,sigma_k). -/
theorem midpoint_dirichlet_kernel_row (a : ℝ) (ha : -1<a) (k : ℕ) :
    midpointKernelRowCLM (kernelTermMap a ha (parityIndex 1 k))=
      (normingRatio a ha (parityIndex 1 k)/norming a (parityIndex 1 k)*
        realSolution a (jacobi.Bessel.sigma a ha (parityIndex 1 k)) (1/2)) •
          realHalfWave a ha (jacobi.Bessel.sigma a ha (parityIndex 1 k)) := by
  ext r
  change kernelTerm a ha (2*k+1) (min (1/2) (1/2)) (halfTime r)=
    (normingRatio a ha (2*k+1)/norming a (2*k+1)*realSolution a (jacobi.Bessel.sigma a ha (2*k+1)) (1/2))*
      realSolution a (jacobi.Bessel.sigma a ha (2*k+1)) (halfTime r)
  rw [min_self,kernelTerm,realSolution_at_reference,midpoint_dirichlet ha k,zero_mul,sub_zero]
  ring

/-- The actual original GL diagonal vanishes exactly at the genuine physical midpoint.
Use: the remaining Neumann midpoint identification and full C2 reflection of the actual target eigenfunctions use w(1/2)=0 without a separate endpoint or asymptotic premise.
Article: jacobi, Proposition C.2.
Proof: the original Dirichlet parity kernel subseries is exactly half of F in the genuine uniform norm. Apply twice the original row extraction and true midpoint transformation. Every unchanged original summand is its source midpoint factor times u(1/2,sigma_(2*k+1)), which is zero by the independently proved exact Dirichlet class. The resulting zero balance is exactly minus the original reconstruction formula for K(1/2,1/2). -/
theorem kernelDiagonal_midpoint_zero (a : ℝ) (ha : -1<a) : kernelDiagonal a ha halfMidpoint=0 := by
  -- The actual source parity row series is uniformly convergent before its original bounded transformation is applied.
  let L := (midpointRowEvaluation a ha).comp midpointKernelRowCLM
  have hK := (parity_kernelTermMap_hasSum a ha 1).const_smul (2:ℝ)
  have hscale : (2:ℝ) • ((1/2:ℝ) • kernelMap a ha)=kernelMap a ha := by rw [smul_smul]; norm_num
  rw [hscale] at hK
  have h := L.hasSum hK
  have hterm (k : ℕ) : L ((2:ℝ) • kernelTermMap a ha (parityIndex 1 k))=0 := by
    rw [map_smul]
    change 2*midpointRowEvaluation a ha (midpointKernelRowCLM (kernelTermMap a ha (parityIndex 1 k)))=0
    rw [midpoint_dirichlet_kernel_row,map_smul,midpointRowEvaluation_wave]
    have hz := (midpointValue_zero_iff a ha (jacobi.Bessel.sigma a ha (parityIndex 1 k):ℂ)).mpr ⟨k,rfl⟩
    rw [hz,Complex.zero_re,smul_zero,mul_zero]
  simp only [hterm] at h
  have hbalance := h.unique hasSum_zero
  change kernel a ha (min (1/2) (1/2)) (min (1/2) (1/2))+
    inner ℝ (solutionRow a ha halfMidpoint) (kernelRowVector a ha halfMidpoint)=0 at hbalance
  rw [min_self,real_inner_comm] at hbalance
  change -kernel a ha (1/2) (1/2)-inner ℝ (kernelRowVector a ha halfMidpoint) (solutionRow a ha halfMidpoint)=0
  linarith

end
end jacobi.GelfandLevitan

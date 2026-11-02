import jacobi.Analytic.GLInverse

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The actual analytic inverse kernel agrees with the previously constructed
original real transformation kernel at every real order in its disk.
The equality includes the full square reconstruction and therefore all
original triangular values and physical transformation integrals.
Use: compares the analytic inverse kernel with the source construction and all original transformed solutions.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original real transformation kernel on its actual closed physical half square.
Use: compares the analytic inverse kernel with the source construction and all original transformed solutions.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def realTransformationMap (a : ℝ) (ha : -1<a) : C(KernelSquare,ℝ) :=
  ⟨fun p => transformationKernel a ha p.1 p.2,transformationKernel_continuous a ha⟩

/-- The original real transformation kernel solves exactly the same continuous-square GL operator equation used by the analytic inverse.
Use: true inverse uniqueness identifies the original real K with its holomorphic continuation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the original physical GL equation and the proved literal prefix product. They have the same point values, integration interval, integrand and normalization; rearrange their three terms. -/
theorem realTransformationMap_equation (a : ℝ) (ha : -1<a) :
    realGLoperator a ha (realTransformationMap a ha)= -realKernelMap a ha := by
  -- The compared equations use the actual original transformation kernel, not a newly prescribed candidate.
  apply ContinuousMap.ext
  rintro ⟨t,s⟩
  change transformationKernel a ha t s+prefixProduct (realTransformationMap a ha) (realKernelMap a ha) (t,s)=
    - jacobi.GelfandLevitan.kernel a ha (t:ℝ) (s:ℝ)
  rw [prefixProduct_subtype]
  have he := transformationKernel_GL a ha t s
  change transformationKernel a ha t s+ jacobi.GelfandLevitan.kernel a ha (t:ℝ) (s:ℝ)+
    (∫ r : Interval in prefixSet (t:ℝ),realTransformationMap a ha (t,halfClamp r)*
      realKernelMap a ha (halfClamp r,s))=0 at he
  linarith

/-- At every real disk order the genuine analytic inverse kernel equals the complex inclusion of the entire original real transformation kernel.
Use: identifies all continued triangular values, transformed waves, profiles and the final energy with the original real construction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual complex operator at real order extends the original real operator. Its original transformation kernel satisfies the same true forcing equation, and the already proved genuine complex inverse makes that solution unique. -/
theorem OrderDisk.GLsolution_real {a0 b : ℝ} (D : OrderDisk a0) (hb : -1<b)
    (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) :
    D.GLsolution (b:ℂ)=continuousOfReal (realTransformationMap b hb) := by
  apply Eq.symm
  apply D.GLsolution_unique (D.GLoperator_real_isUnit hb hbd)
  rw [D.GLoperator_real hb hbd,realTransformationMap_equation,D.kernelMap_real hb hbd]
  ext p
  simp only [continuousOfReal,ContinuousMap.coe_mk,ContinuousMap.neg_apply,_root_.Complex.ofReal_neg]

end
end jacobi.Analytic

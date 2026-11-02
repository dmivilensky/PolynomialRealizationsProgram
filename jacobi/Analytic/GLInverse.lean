import jacobi.Analytic.GLBaseInverse

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The actual continuous-kernel GL operator has a common complex neighborhood
with a uniformly bounded genuine inverse. Applying that inverse to the
original kernel forcing gives a norm-holomorphic continuous solution.
This construction concerns the literal physical GL prefix integral.
Use: supplies the continued transformation kernel and its original transformed solutions and energy.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual continuous-kernel GL solution obtained by the true bounded inverse of the original operator.
Use: supplies the continued transformation kernel and its original transformed solutions and energy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def OrderDisk.GLsolution {a0 : ℝ} (D : OrderDisk a0) (a : ℂ) : C(KernelSquare,ℂ) :=
  -(Ring.inverse (D.GLoperator a) (D.kernelMap a))

/-- The original continuous GL operator has a genuine common closed complex neighborhood with uniformly bounded true inverse.
Use: the analytic GL solution exists on one order disk independently of both physical coordinates and all spectral indices.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual base operator is a proved unit and the genuine family is operator-norm continuous. Units form an open subset of the Banach algebra, and inversion is continuous there. Keep both properties and an enlarged base inverse norm on one closed smaller order disk. -/
theorem OrderDisk.GLoperator_local_inverse {a0 : ℝ} (D : OrderDisk a0) (ha0 : -1<a0) :
    ∃ r M : ℝ,0<r ∧ r<D.radius ∧ 0<M ∧
      ∀ a : ℂ,‖a-(a0:ℂ)‖≤r → IsUnit (D.GLoperator a) ∧ ‖Ring.inverse (D.GLoperator a)‖≤M := by
  -- The neighborhood is obtained from the proved real base inverse, not from an invertibility premise.
  have hbase : ‖(a0:ℂ)-(a0:ℂ)‖≤D.radius := by simpa only [sub_self,norm_zero] using D.radius_pos.le
  have hu := D.GLoperator_real_isUnit ha0 hbase
  have hA := (D.GLoperator_holomorphic.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self D.radius_pos))).continuousAt
  have hi : ContinuousAt Ring.inverse (D.GLoperator (a0:ℂ)) := by
    simpa only [IsUnit.unit_spec] using
      NormedRing.inverse_continuousAt (R := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) hu.unit
  have hI := hi.comp (f := D.GLoperator) hA
  have hc := continuous_norm (E := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ))
  have hInorm : ContinuousAt (fun a : ℂ => ‖Ring.inverse (D.GLoperator a)‖) (a0:ℂ) :=
    hc.continuousAt.comp (f := fun a : ℂ => Ring.inverse (D.GLoperator a)) hI
  let M : ℝ := ‖Ring.inverse (D.GLoperator (a0:ℂ))‖+1
  have hM : 0<M := by dsimp [M]; positivity
  have hunit : ∀ᶠ a in 𝓝 (a0:ℂ),IsUnit (D.GLoperator a) :=
    hA.eventually ((Units.isOpen (R := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ))).mem_nhds hu)
  have hnorm : ∀ᶠ a in 𝓝 (a0:ℂ),‖Ring.inverse (D.GLoperator a)‖<M :=
    hInorm.eventually_lt_const (by dsimp [M]; linarith)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp (hunit.and hnorm)
  let r : ℝ := min (D.radius/2) (ε/2)
  have hr : 0<r := lt_min (half_pos D.radius_pos) (half_pos hε)
  have hrD : r<D.radius := (min_le_left _ _).trans_lt (by linarith [D.radius_pos])
  refine ⟨r,M,hr,hrD,hM,fun a ha => ?_⟩
  have hm : a∈ball (a0:ℂ) ε := by
    rw [mem_ball,dist_eq_norm]
    exact ha.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  exact ⟨(hsub hm).1,(hsub hm).2.le⟩

/-- The genuine inverse GL solution solves exactly the original continuous-kernel operator equation wherever that actual operator is invertible.
Use: yields the literal physical GL equation by the proved prefix-integral representation, and gives uniqueness by the same true inverse.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the genuine right inverse identity at the original kernel forcing and use complex linearity for its negative. -/
theorem OrderDisk.GLsolution_equation {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (hu : IsUnit (D.GLoperator a)) : D.GLoperator a (D.GLsolution a)= -D.kernelMap a := by
  have he := congrArg (fun T : C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ) => T (D.kernelMap a))
    (Ring.mul_inverse_cancel _ hu)
  change D.GLoperator a (Ring.inverse (D.GLoperator a) (D.kernelMap a))=D.kernelMap a at he
  rw [OrderDisk.GLsolution,map_neg,he]

/-- Every continuous square solution of the genuine continued GL equation equals the actual inverse solution.
Use: identifies the analytic construction with original real transformation kernels and independently constructed candidates.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual operator is a proved unit and hence injective; compare the two genuine images of the same original forcing. -/
theorem OrderDisk.GLsolution_unique {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (hu : IsUnit (D.GLoperator a)) {K : C(KernelSquare,ℂ)}
    (hK : D.GLoperator a K= -D.kernelMap a) : K=D.GLsolution a :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1 (hK.trans (D.GLsolution_equation hu).symm)

/-- The genuine continuous GL inverse solution is holomorphic in its actual kernel norm on every open order subdisk where the original operator remains invertible.
Use: supplies pointwise order holomorphy of K, the analytic transformed waves and the continued energy c_star.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual operator and forcing are already norm holomorphic. Inversion is analytic at every proved Banach-algebra unit; compose it with the true operator curve, apply the resulting bounded inverse to the original analytic forcing, and negate. -/
theorem OrderDisk.GLsolution_holomorphic {a0 r : ℝ} (D : OrderDisk a0)
    (hrD : r≤D.radius)
    (hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a)) :
    DifferentiableOn ℂ D.GLsolution (ball (a0:ℂ) r) := by
  -- Both analytic factors take values in fixed original Banach spaces before the actual inverse evaluation.
  intro a ha
  have haD : a∈ball (a0:ℂ) D.radius := ball_subset_ball hrD ha
  have hA := D.GLoperator_holomorphic.analyticOnNhd
    (E := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) isOpen_ball a haD
  have hK := D.kernelMap_holomorphic.differentiableAt (isOpen_ball.mem_nhds haD)
  have hi : AnalyticAt ℂ Ring.inverse (D.GLoperator a) := by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℂ) (A := C(KernelSquare,ℂ) →L[ℂ] C(KernelSquare,ℂ)) (hunit a ha).unit)
  have hInv := (hi.comp (f := D.GLoperator) hA).differentiableAt
  exact (hInv.clm_apply hK).neg.differentiableWithinAt

end
end jacobi.Analytic

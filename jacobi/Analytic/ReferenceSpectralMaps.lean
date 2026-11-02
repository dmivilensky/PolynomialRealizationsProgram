import jacobi.Analytic.GLUniform

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The actual moving-spectral reference functions form a holomorphic family
in the Banach space of continuous physical half-interval functions.
The original full-index amplitude estimate holds in that same norm.
Use: packages the original functions as genuine continuous-function Banach vectors before analytic GL transformation.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric jacobi.ComplexReference jacobi.GelfandLevitan
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] jacobi.ComplexReference.solution

/-- The actual reference function at a continued original Bessel energy is spatially continuous up to both physical half-interval endpoints.
Use: packages the original functions as genuine continuous-function Banach vectors before analytic GL transformation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original reference energy solution is jointly continuous, including zero frequency and the singular spatial endpoint. Restrict order and energy to their actual fixed spectral values. -/
theorem OrderDisk.reference_spatial_continuous {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k : ℕ) :
    Continuous (fun t : HalfInterval => solution a (D.spectrum k a) t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hag : 0<(gamma a).re := by have har := D.admissible ha; unfold gamma; norm_num; linarith
  exact (solution_joint_continuous (z := D.spectrum k a) hag ⟨t.property.1,by linarith [t.property.2]⟩).comp_of_eq
    (f := fun s : HalfInterval => (a,D.spectrum k a,(s:ℝ)))
    (show ContinuousAt (fun s : HalfInterval => (a,D.spectrum k a,(s:ℝ))) t by fun_prop) rfl

/-- The genuine target-spectral reference function in the physical continuous-function Banach space.
Use: applies the analytic original GL transformation to the same spectral reference function that defines the article's u and Phi_k.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The zero value outside the estimation disk only totalizes the Lean function; all assertions concern its original disk. -/
def OrderDisk.referenceMap {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (a : ℂ) : C(HalfInterval,ℂ) :=
  if ha : ‖a-(a0:ℂ)‖≤D.radius then
    ⟨fun t => solution a (D.spectrum k a) t,D.reference_spatial_continuous ha k⟩ else 0

/-- The continuous reference vector evaluates to the actual original moving-spectral solution at every disk order.
Use: identifies its norm bounds and analytic GL transformation with the literal source reference factors.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the genuine disk branch of the definition is selected and continuous evaluation reduces to the original solution. -/
theorem OrderDisk.referenceMap_apply {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k : ℕ) (t : HalfInterval) :
    D.referenceMap k a t=solution a (D.spectrum k a) t := by
  simp only [OrderDisk.referenceMap,dite_eq_left ha,ContinuousMap.coe_mk]

/-- The genuine target-spectral reference vectors are norm-continuous on the common closed complex order disk.
Use: supplies Banach-valued holomorphy and actual spatial continuity for the transformed spectral solutions.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual spectral branches are continuous on a larger disk, and the original energy solutions are jointly continuous. Restrict to the compact physical half interval and curry this genuine joint continuity into the continuous-function norm. -/
theorem OrderDisk.referenceMap_continuousOn {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    ContinuousOn (D.referenceMap k) (closedBall (a0:ℂ) D.radius) := by
  -- The same original spectral branch is used in the spatial and parameter coordinates.
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  intro p hp
  let U := closedBall (a0:ℂ) D.radius ×ˢ (univ : Set HalfInterval)
  have hfst : ContinuousWithinAt (fun q : ℂ × HalfInterval => q.1) U p := continuousWithinAt_fst
  have htime : ContinuousWithinAt (fun q : ℂ × HalfInterval => (q.2:ℝ)) U p := by fun_prop
  have hS : ContinuousOn (D.spectrum k) (closedBall (a0:ℂ) D.radius) :=
    (D.holomorphic k).continuousOn.mono (closedBall_subset_ball (by linarith [D.radius_pos]))
  have hSp := (hS p.1 hp.1).comp hfst (fun _ hq => hq.1)
  have hag : 0<(gamma p.1).re := by
    have har := D.admissible (by simpa only [mem_closedBall,dist_eq_norm] using hp.1)
    unfold gamma
    norm_num
    linarith
  have hsol := (solution_joint_continuous (z := D.spectrum k p.1) hag
    ⟨p.2.property.1,by linarith [p.2.property.2]⟩).comp_continuousWithinAt
      (f := fun q : ℂ × HalfInterval => (q.1,D.spectrum k q.1,(q.2:ℝ)))
      (hfst.prodMk (hSp.prodMk htime))
  apply hsol.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact D.referenceMap_apply (by simpa only [mem_closedBall,dist_eq_norm] using hq.1) k q.2

/-- The actual reference vectors at the continued original Bessel energies are holomorphic in the physical continuous-function norm.
Use: their bounded bilinear transformation by the true analytic GL kernel gives the original holomorphic u(t,sigma_k).
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the true spectral energy branch and order are analytic, so each original reference value is holomorphic by the proved energy-series theorem. The actual continuous-function family is norm-continuous; apply the proved Banach-valued Cauchy theorem. -/
theorem OrderDisk.referenceMap_holomorphic {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    DifferentiableOn ℂ (D.referenceMap k) (ball (a0:ℂ) D.radius) := by
  -- The entire energy dependence avoids any analyticity assumption about a frequency square root.
  apply continuousMap_differentiableOn isOpen_ball ((D.referenceMap_continuousOn k).mono ball_subset_closedBall)
  intro t a ha
  have had : ‖a-(a0:ℂ)‖≤D.radius := le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha)
  have hag : 0<(gamma a).re := by have har := D.admissible had; unfold gamma; norm_num; linarith
  have hS := (D.holomorphic k).analyticOnNhd isOpen_ball a
    (ball_subset_ball (by linarith [D.radius_pos]) ha)
  have hsol := solution_comp_analytic analyticAt_id hS hag
    (show (t:ℝ)∈Ico 0 1 from ⟨t.property.1,by linarith [t.property.2]⟩)
  apply hsol.differentiableAt.differentiableWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact D.referenceMap_apply
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hb)) k t
  · exact D.referenceMap_apply had k t

/-- The original moving-spectral reference vectors have their full uniform index-power bound in the actual continuous-function norm.
Use: the analytic GL transformation and actual norming denominator cancel these same powers in the original profile-series majorant.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: apply the proved full-index actual spectral reference estimate at every physical point and the community continuous-function supremum-norm criterion. -/
theorem OrderDisk.referenceMap_bounds {a0 : ℝ} (D : OrderDisk a0) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ‖D.referenceMap k a‖≤C/(k+1:ℝ)^(gamma a).re := by
  obtain ⟨C,hC,hbound⟩ := D.reference_spectral_bounds
  refine ⟨C,hC,fun a ha k => ?_⟩
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [D.referenceMap_apply ha k t]
  exact (hbound a ha k t t.property).1

end
end jacobi.Analytic

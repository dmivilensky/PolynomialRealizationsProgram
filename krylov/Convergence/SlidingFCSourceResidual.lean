import krylov.Convergence.SlidingFCResidual

/-!
Article: main_krylov, thm:G, sharp finite sliding FC source estimate.
Use: bound the true terminal gradient from actual function derivatives and
observations, without a model-error or recurrence assumption.
Source: genuine segment Hessian averages, Schwarz symmetry, the exact FC
staircase, and reconstruction in the real normalized chronological frame.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Two actual segment secants have the sharp half-weight endpoint
comparison on any convex source domain. -/
omit [CompleteSpace E] in
theorem source_segment_comparison (H : E → E →L[ℝ] E)
    (S : Set E) (hS : Convex ℝ S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (a b c d : E) (ha : a∈S) (hb : b∈S) (hc : c∈S) (hd : d∈S) :
    ‖averagedDerivative H a (b-a)-averagedDerivative H c (d-c)‖≤
      (L:ℝ)/2*(‖a-c‖+‖b-d‖) := by
  have hp t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈S :=
    hS.add_smul_mem ha (by simpa only [add_sub_cancel] using hb) ht
  have hq t (ht : t∈Icc (0:ℝ) 1) : c+t • (d-c)∈S :=
    hS.add_smul_mem hc (by simpa only [add_sub_cancel] using hd) ht
  have cp := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
  have cq := hH.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hq
  simpa only [add_sub_cancel] using averagedHessian_endpoint_bound H a (b-a) c (d-c)
    L cp cq L.coe_nonneg (fun t ht=>hH.norm_sub_le (hp t ht) (hq t ht))

/-- A genuine segment inside the open source ball is selfadjoint, directly
from the scalar objective's actual first and second derivatives. -/
theorem source_segment_symmetric (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} {L : ℝ≥0} (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:E) r,HasFDerivAt G (H z) z)
    (a b : E) (ha : ‖a‖<r) (hb : ‖b‖<r) :
    (averagedDerivative H a (b-a)).toLinearMap.IsSymmetric := by
  have hp t (ht : t∈Icc (0:ℝ) 1) : ‖a+t • (b-a)‖<r :=
    (segment_norm_le_endpoints a b (max ‖a‖ ‖b‖) (le_max_left _ _)
      (le_max_right _ _) t ht).trans_lt (max_lt ha hb)
  have hm t (ht : t∈Icc (0:ℝ) 1) : a+t • (b-a)∈Metric.closedBall (0:E) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hp t ht).le
  exact averagedDerivative_symmetric H a (b-a)
    (hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hm)
    (fun t ht=>genuine_hessian_symmetric (ContinuousLinearEquiv.refl ℝ E) f G H
      (fun z hz=>hf z (by change ‖z‖≤r at hz; simpa only [Metric.mem_closedBall,dist_zero_right] using hz))
      (fun z hz=>hG z (by change ‖z‖≤r at hz; simpa only [Metric.mem_closedBall,dist_zero_right] using hz))
      _ (by simpa only [ContinuousLinearEquiv.refl_apply] using hp t ht))

/-- The printed finite FC residual bound, with its exact factor 4 and
(dimension−1)^(3/2), for a genuine function on its actual observed path.
Line stationarity and observed conjugacy are the two exact executor
identities; no independence or model approximation is assumed. -/
theorem source_conjugate_path_residual
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    {r : ℝ} {L : ℝ≥0} (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+1))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+1))) r,HasFDerivAt G (H z) z)
    (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) {r₀ r₁ : ℝ} (hr₀ : 0≤r₀) (hr₁ : 0≤r₁)
    (hmem : ∀ j≤n+1,‖x j‖<r) (hball : ∀ j≤n+1,‖x j‖≤r₀)
    (hnew : ∀ j,0<j → j≤n+1 → ‖x j‖≤r₁)
    (hline : ∀ j<n+1,inner ℝ (x (j+1)-x j) (G (x (j+1)))=0)
    (hconj : ∀ i j,i<j → j<n+1 →
      inner ℝ (G (x (i+1))-G (x i)) (x (j+1)-x j)=0)
    (hu : IsUnit (windowMatrix (unitWindow (windowStep (n:=n+1) x 0))).det) :
    ‖G (x (n+1))‖≤‖(windowMatrix (unitWindow (windowStep (n:=n+1) x 0)))⁻¹‖*
      (Real.sqrt n*((n:ℝ)*(4*(L:ℝ)*r₀*r₁))) := by
  let A := fun j=>averagedDerivative H (x j) (x (j+1)-x j)
  have hm j (hj : j≤n+1) : x j∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+1))) r := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (hmem j hj).le
  have hy j (hj : j<n+1) : G (x (j+1))-G (x j)=A j (x (j+1)-x j) := by
    have hp t (ht : t∈Icc (0:ℝ) 1) : x j+t • (x (j+1)-x j)∈Metric.closedBall 0 r :=
      (convex_closedBall _ _).add_smul_mem (hm j (by omega))
        (by simpa only [add_sub_cancel] using hm (j+1) (by omega)) ht
    have he := averagedDerivative_apply G H (x j) (x (j+1)-x j)
      (hH.continuousOn.comp (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp)
      (fun t ht=>hG _ (hp t ht))
    simpa only [A,add_sub_cancel] using he.symm
  have hsym j (hj : j<n+1) : (A j).toLinearMap.IsSymmetric :=
    source_segment_symmetric f G H hH hf hG _ _ (hmem j (by omega)) (hmem (j+1) (by omega))
  have hd i j (_hij : i<j) (hj : j<n+1) : ‖A j-A i‖≤2*(L:ℝ)*r₀ := by
    have hh := source_segment_comparison H (Metric.closedBall 0 r) (convex_closedBall _ _) hH
      (x j) (x (j+1)) (x i) (x (i+1)) (hm j (by omega)) (hm (j+1) (by omega))
      (hm i (by omega)) (hm (i+1) (by omega))
    apply hh.trans
    have h₁ := (norm_sub_le (x j) (x i)).trans (add_le_add (hball j (by omega)) (hball i (by omega)))
    have h₂ := (norm_sub_le (x (j+1)) (x (i+1))).trans
      (add_le_add (hball (j+1) (by omega)) (hball (i+1) (by omega)))
    nlinarith [L.coe_nonneg]
  have hstep j (hj₀ : 0<j) (hj : j<n+1) : ‖x (j+1)-x j‖≤2*r₁ := by
    have hh := (norm_sub_le (x (j+1)) (x j)).trans
      (add_le_add (hnew (j+1) (by omega) (by omega)) (hnew j hj₀ (by omega)))
    linarith
  apply full_frame_residual_bound _ _ hu (by positivity)
  · simp only [unitWindow,rescaleWindow,windowStep,Nat.zero_add,Fin.val_last,
      real_inner_smul_left,hline n (by omega),mul_zero]
  · intro i
    have hh := conjugate_staircase_coordinate_bound (fun j=>G (x j))
      (fun j=>x (j+1)-x j) A (n+1) (by positivity : 0≤2*(L:ℝ)*r₀)
      (by positivity : 0≤2*r₁) hy hsym hline hconj hd hstep (i:=i.val) (by omega)
    rw [show n+1-1=n by omega] at hh
    simpa only [unitWindow,rescaleWindow,windowStep,Nat.zero_add,Nat.add_sub_cancel,
      Fin.val_castSucc] using hh.trans_eq (by ring)

end
end krylov.Convergence

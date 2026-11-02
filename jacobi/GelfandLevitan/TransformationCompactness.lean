import jacobi.GelfandLevitan.RowIntegrals
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Continuity of the actual zero-extended GL rows makes the Volterra
operator compact by Arzela--Ascoli. This reuses the already proved
Hilbert row continuity and avoids a separate approximation theorem
for discontinuous triangular kernels.
Use: community Arzela--Ascoli proves its compactness before the genuine L2 inclusion.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace BoundedContinuousFunction
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] solutionRow

/-- The actual Volterra action in bounded continuous functions on the original compact physical domain.
Use: community Arzela--Ascoli proves its compactness before the genuine L2 inclusion.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformationBoundedAction (a : ℝ) (ha : -1<a) : halfSubspace →L[ℝ] (Interval →ᵇ ℝ) :=
  (ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    transformationActionCLM a ha

/-- The genuine Volterra action on the original Hilbert unit ball is an equicontinuous family.
Use: Arzela--Ascoli proves transformationBoundedAction_compact for the actual operator.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: Cauchy--Schwarz and the community metric equicontinuity criterion.
Proof: a unit input changes its output by at most the norm difference of the two actual solution rows. Their proved Hilbert-norm continuity gives one common modulus, independent of the input. -/
theorem transformationAction_equicontinuous (a : ℝ) (ha : -1<a) :
    Equicontinuous ((↑) :
      (transformationBoundedAction a ha '' Metric.closedBall 0 1) → Interval → ℝ) := by
  -- The single actual row modulus controls every genuine unit input at once.
  intro t
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  have hR : Continuous (fun s:Interval => solutionRow a ha (halfClamp s)) :=
    (solutionRow_continuous a ha).comp halfClamp.continuous
  filter_upwards [hR.continuousAt.eventually (Metric.ball_mem_nhds _ hε)] with s hs
  intro f
  obtain ⟨v,hv,hf⟩ := f.property
  have hv' : ‖v‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  change dist ((f:Interval →ᵇ ℝ) t) ((f:Interval →ᵇ ℝ) s)<ε
  rw [← hf]
  change dist (inner ℝ (solutionRow a ha (halfClamp t)) v)
    (inner ℝ (solutionRow a ha (halfClamp s)) v)<ε
  rw [dist_eq_norm,← inner_sub_left]
  calc
    _ ≤ ‖solutionRow a ha (halfClamp t)-solutionRow a ha (halfClamp s)‖*‖v‖ := norm_inner_le_norm _ _
    _ ≤ ‖solutionRow a ha (halfClamp t)-solutionRow a ha (halfClamp s)‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hv'
    _ < ε := by
      have hs' : dist (solutionRow a ha (halfClamp s)) (solutionRow a ha (halfClamp t))<ε := hs
      rw [dist_comm,dist_eq_norm] at hs'
      exact hs'

/-- The actual Volterra action into bounded continuous functions is compact.
Use: postcomposing with the original continuous-to-L2 embedding proves compactness of the true transformationOperator.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: Arzela--Ascoli, mathlib.
Proof: all genuine unit-ball outputs take values in the same compact real interval by Cauchy--Schwarz. The independently proved row modulus makes that whole family equicontinuous. Arzela--Ascoli gives compact closure of its actual image. -/
theorem transformationBoundedAction_compact (a : ℝ) (ha : -1<a) :
    IsCompactOperator (transformationBoundedAction a ha) := by
  -- Compactness is proved for the true operator, not assumed from a formal kernel name.
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (transformationBoundedAction a ha).toLinearMap (by norm_num : (0:ℝ)<1)).mpr
  refine BoundedContinuousFunction.arzela_ascoli (Icc (-‖solutionRowMap a ha‖) ‖solutionRowMap a ha‖)
    isCompact_Icc _ (fun f t hf => ?_) (transformationAction_equicontinuous a ha)
  obtain ⟨v,hv,rfl⟩ := hf
  have hv' : ‖v‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hb : |transformationBoundedAction a ha v t|≤‖solutionRowMap a ha‖ := by
    change ‖inner ℝ (solutionRow a ha (halfClamp t)) v‖≤_
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hv').trans ((solutionRowMap a ha).norm_coe_le_norm _))
  exact abs_le.mp hb

/-- The actual original Volterra transformation operator is compact on the physical half-interval Hilbert space.
Use: the exact GL factorization and compact Fredholm alternative prove its identity perturbation invertible for the two-bases argument.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the actual continuous action is compact by Arzela--Ascoli; the genuine bounded-function equivalence and original row embedding are bounded linear maps, so their postcomposition preserves compactness. -/
theorem transformationOperator_compact (a : ℝ) (ha : -1<a) :
    IsCompactOperator (transformationOperator a ha) := by
  -- The bounded-function equivalence cancels exactly, leaving the original continuous-to-L2 row embedding.
  have h := (transformationBoundedAction_compact a ha).clm_comp
    (rowEmbedding ∘L (ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have he : (rowEmbedding ∘L
      (ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
        transformationBoundedAction a ha=transformationOperator a ha := by
    apply ContinuousLinearMap.ext
    intro v
    change rowEmbedding ((ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ).symm
      ((ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ) (transformationActionMap a ha v)))=
        rowEmbedding (transformationActionMap a ha v)
    rw [LinearIsometryEquiv.symm_apply_apply]
  change IsCompactOperator (((rowEmbedding ∘L
    (ContinuousMap.linearIsometryBoundedOfCompact Interval ℝ ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap) ∘L
      transformationBoundedAction a ha)) at h
  rwa [he] at h

end
end jacobi.GelfandLevitan

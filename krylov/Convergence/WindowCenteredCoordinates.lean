import krylov.Convergence.WindowTranslation
import krylov.Convergence.WindowMetricRegularity

/-!
Article: main_krylov, thm:grow and cor:xrF, actual centered metric source.
Use: reconstruct genuine scalar, gradient and Hessian data at an arbitrary
physical limit; transfer the literal observable SS1-F executor exactly.
Source: Frechet chain rule, positive-root congruence and actual endpoint
translation identities.
-/
namespace krylov.Convergence
noncomputable section
open Set Filter Topology krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original scalar objective in the actual centered metric. -/
def centeredMetricObjective (T : E ≃L[ℝ] E) (c : E) (f : E → ℝ) : E → ℝ :=
  coordinateObjective T (fun z=>f (c+z))

/-- The genuine dual gradient field of the centered metric objective. -/
def centeredMetricGradient (T : E ≃L[ℝ] E) (c : E) (G : E → E) : E → E :=
  coordinateGradient T (fun z=>G (c+z))

/-- The genuine inverse-congruence Hessian field in the centered metric. -/
def centeredMetricHessian (T : E ≃L[ℝ] E) (c : E) (H : E → E →L[ℝ] E) : E → E →L[ℝ] E :=
  coordinateDerivative T (fun z=>H (c+z))

/-- The actual physical source domain expressed in centered coordinates. -/
def centeredMetricDomain (T : E ≃L[ℝ] E) (c : E) (S : Set E) : Set E :=
  (fun y=>c+T.symm y) ⁻¹' S

/-- Convexity is preserved by the real affine coordinate map. -/
theorem centeredMetricDomain_convex (T : E ≃L[ℝ] E) (c : E) {S : Set E}
    (hS : Convex ℝ S) : Convex ℝ (centeredMetricDomain T c S) := by
  exact (hS.affine_preimage (AffineMap.const ℝ _ c+AffineMap.id ℝ _)).linear_preimage T.symm.toLinearMap

/-- An actual neighborhood of the physical limit becomes a neighborhood
of zero under the constructed centered metric. -/
theorem centeredMetricDomain_mem_nhds (T : E ≃L[ℝ] E) (c : E) {S : Set E}
    (hS : S∈𝓝 c) : centeredMetricDomain T c S∈𝓝 (0:E) := by
  exact (continuous_const.add T.symm.continuous).continuousAt.preimage_mem_nhds
    (by simpa only [Pi.add_apply,map_zero,add_zero] using hS)

/-- The actual scalar pullback has precisely the displayed true gradient. -/
theorem centeredMetricObjective_hasFDerivAt (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (c : E) (f : E → ℝ) (G : E → E)
    (y : E) (hf : HasFDerivAt f (innerSL ℝ (G (c+T.symm y))) (c+T.symm y)) :
    HasFDerivAt (centeredMetricObjective T c f) (innerSL ℝ (centeredMetricGradient T c G y)) y := by
  have hfc : HasFDerivAt (fun z=>f (c+z)) (innerSL ℝ (G (c+T.symm y))) (T.symm y) := by
    have hh := hf.comp (T.symm y) ((hasFDerivAt_id (T.symm y)).const_add c)
    convert! hh using 1
  exact coordinateObjective_hasFDerivAt T hT _ _ y hfc

/-- Actual gradient differentiation commutes with the centered metric. -/
theorem centeredMetricGradient_hasFDerivAt (T : E ≃L[ℝ] E) (c : E) (G : E → E)
    (H : E → E →L[ℝ] E) (y : E)
    (hG : HasFDerivAt G (H (c+T.symm y)) (c+T.symm y)) :
    HasFDerivAt (centeredMetricGradient T c G) (centeredMetricHessian T c H y) y := by
  have hGc : HasFDerivAt (fun z=>G (c+z)) (H (c+T.symm y)) (T.symm y) := by
    have hh := hG.comp (T.symm y) ((hasFDerivAt_id (T.symm y)).const_add c)
    convert! hh using 1
  exact coordinateGradient_hasFDerivAt T _ _ y hGc

/-- Centering and the true metric root preserve the complete observable
SS1-F trajectory, including all scalar observations and chosen splits. -/
theorem ss1FObservedSequence_centered_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (c : E) (f : E → ℝ) (G : E → E)
    (seed : Fin (n+2) → E) (j : ℕ) :
    T (ss1FSequence f G (ss1FObservedSplit G) seed j-c)=
      ss1FSequence (centeredMetricObjective T c f) (centeredMetricGradient T c G)
        (ss1FObservedSplit (centeredMetricGradient T c G)) (fun i=>T (seed i-c)) j := by
  rw [ss1FObservedSequence_translate]
  exact ss1FObservedSequence_coordinate T hT _ _ _ j

/-- The actual physical Hessian Lipschitz allowance yields exactly the
printed cubic inverse-root factor for a centered source. -/
theorem centeredMetricHessian_lipschitz {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (c : EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {S : Set (EuclideanSpace ℝ (Fin n))} {L : NNReal} (hH : LipschitzOnWith L H S)
    {mu : ℝ} (hmu : 0<mu)
    (hlower : ∀ v,mu*‖v‖^2≤ inner ℝ v (krylov.Reference.cgOperator base v)) :
    LipschitzOnWith (Real.toNNReal ((L:ℝ)*mu^(-(3/2:ℝ))))
      (centeredMetricHessian (metricCoordinates base hb) c H)
      (centeredMetricDomain (metricCoordinates base hb) c S) := by
  have hc : LipschitzOnWith L (fun z=>H (c+z)) ((fun z=>c+z) ⁻¹' S) := by
    rw [lipschitzOnWith_iff_norm_sub_le] at hH ⊢
    intro z hz w hw
    have hh := hH hz hw
    have he : c+z-(c+w)=z-w := by abel_nf
    simpa only [he] using hh
  exact metric_hessian_lipschitz_bound base hb _ hc hmu hlower

end
end krylov.Convergence

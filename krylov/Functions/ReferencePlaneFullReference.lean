import krylov.Functions.ReferencePlanePrintedNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), full original own-reference admission.
Use: preserve all n genuine active atoms of the actual first-segment secant
and the actual scaled scalar initial gradient. Source: the actual rational
CG recurrence, open nonstagnation and the ambient spectral-cardinality bound.
-/
namespace krylov.Functions
noncomputable section
open Matrix Filter Topology krylov.Correction krylov.Reference krylov.Nonlinear krylov.Stability krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every sufficiently close positive matrix preserves a genuinely full
reference, without a supplied nonstagnation condition on the perturbed base.
Article: main_krylov, prop:Fcycle(iii), actual n-atom reference admission. -/
theorem reference_full_count_neighborhood
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hn : 0<n) (hfull : referenceAtomCount A hA g=n) :
    ∃ δ : ℝ, 0<δ ∧ ∀ B : Matrix (Fin n) (Fin n) ℝ, ∀ hB : B.PosDef,
      ‖B-A‖≤δ → referenceAtomCount B hB g=n := by
  let k := n-1
  have hk : k<referenceAtomCount A hA g := by dsimp only [k]; omega
  have hpre (j : ℕ) (hj : j<k) : CG.gradient (cgOperator A) g j≠0 :=
    cg_nonstagnation A hA g j (hj.trans hk)
  let Q := fun Δ : Matrix (Fin n) (Fin n) ℝ=>cgOperator (A+Δ)
  have hQa : AnalyticAt ℝ Q 0 := by
    exact (matrixOperator_contDiffAt (fun Δ : Matrix (Fin n) (Fin n) ℝ=>A+Δ) 0
      (analyticAt_const.add analyticAt_id).contDiffAt).analyticAt
  have hp := cgOperator_positive A hA
  have hG := (cg_prefix_analytic Q (fun _=>g) 0 hQa analyticAt_const
    (by simpa only [Q,add_zero] using hp.1) (by simpa only [Q,add_zero] using hp.2) k
    (by simpa only [Q,add_zero] using hpre)).1.continuousAt.norm
  have hgn : 0<‖CG.gradient (cgOperator A) g k‖ := norm_pos_iff.mpr (cg_nonstagnation A hA g k hk)
  have he : ∀ᶠ Δ : Matrix (Fin n) (Fin n) ℝ in 𝓝 0, 0<‖CG.gradient (Q Δ) g k‖ := by
    apply hG.preimage_mem_nhds
    apply isOpen_Ioi.mem_nhds
    change 0<‖CG.gradient (Q 0) g k‖
    simpa only [Q,add_zero] using hgn
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro B hB hBδ
  have hb := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hBδ.trans_lt (half_lt_self hδ))
  change 0<‖CG.gradient (cgOperator (A+(B-A))) g k‖ at hb
  rw [add_sub_cancel] at hb
  have hactive : k<referenceAtomCount B hB g := by
    by_contra hh
    have hz := (cg_stopping_iff B hB g k).mpr (by omega)
    rw [hz,norm_zero] at hb
    exact (lt_irrefl 0) hb
  have hle : referenceAtomCount B hB g≤n := by
    unfold referenceAtomCount activeSpectralValues
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
  dsimp only [k] at hactive
  omega

/-- The actual observed first matrix of every sufficiently small genuine
full-reference cubic source has n atoms with its actual initial gradient.
Positivity is independently derived by `referencePlane_own_normalization`.
Article: main_krylov, prop:Fcycle(iii), original full reference scope. -/
theorem referencePlane_observed_full_count
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hn : 2≤n) (hfull : referenceAtomCount A hA g=n) (U : ℝ) (hU : 0<U) :
    ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ∀ hB : (referencePlaneObservedMatrix A hA g ε (scaleBinaryCubic α t)).PosDef,
      referenceAtomCount (referencePlaneObservedMatrix A hA g ε (scaleBinaryCubic α t)) hB
        (gradient (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t)) 0)=n := by
  have hN : 2≤referenceAtomCount A hA g := by omega
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  obtain ⟨δ,hδ,hclose⟩ := reference_full_count_neighborhood A hA g (by omega) hfull
  obtain ⟨L,hL,hLt⟩ := planeTerminal_uniform_bounds (referencePlaneRatio A hA g)
  let J := ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*
    (U*‖canonicalCGStep A g 0‖*(1/2+L+‖planeOfPair (1,referencePlaneRatio A hA g)‖))
  have hJ : 0≤J := by dsimp only [J]; positivity
  refine ⟨δ/(J+1),div_pos hδ (by positivity),?_⟩
  intro ε hε heps α hα hαU t ht hB
  rw [referencePlaneCubicObjective_initial_gradient A hA g hN hε,
    referenceAtomCount_scalar _ hB g ε hε.ne']
  apply hclose _ hB
  have hb := metricHilbertPlaneFirstSecant_scaled_drift A hA _ _ he hh heh
    (canonicalCGStep A g 0) (referencePlaneRatio A hA g) U ε α hε.le hα hαU ht
  have hbound : ‖referencePlaneObservedMatrix A hA g ε (scaleBinaryCubic α t)-A‖≤J*ε := by
    apply hb.trans
    dsimp only [J]
    gcongr
    exact (hLt t ht).1
  have hsmall := (lt_div_iff₀ (by positivity : 0<J+1)).mp heps
  exact hbound.trans (by nlinarith only [hsmall,hε])

end
end krylov.Functions

import krylov.Functions.ReferencePlaneAverageContinuity
import krylov.Functions.NormalizedReferenceCompact
import krylov.Functions.PlanarRFCFWorst

/-!
Article: main_krylov, s7:N and prop:Fcycle(iii), actual compact admission.
Use: place all actual normalized first-secant/initial-gradient pairs of the
full sharp source family in one derived compact set of genuine n-atom
positive references. Source: actual affine midpoint continuity, compactness
of the genuine binary ball and open full-CG nonstagnation.
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Metric NormedSpace krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Positive normalization preserves all genuine quadratic-reference
properties. Article: main_krylov, s7:N. -/
theorem normalizedReference_nondegenerate
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (hpre : ∀ i<N, CG.gradient Q g i≠0) :
    let z := normalizedReference Q g
    z.1.toLinearMap.IsSymmetric ∧ (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧
      ∀ i<N, CG.gradient z.1 z.2 i≠0 := by
  have hQne : Q≠0 := by
    intro hz
    have hp := hpos g hg
    simp only [hz,_root_.zero_apply,inner_zero_right] at hp
    exact (lt_irrefl 0) hp
  have hq : 0<‖Q‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hQne)
  have hg' : 0<‖g‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hg)
  refine ⟨?_,?_,positive_scaled_reference_nondegenerate Q hQ hpos g _ _ hq hg' N hpre⟩
  · intro x y
    change inner ℝ ((‖Q‖⁻¹ • Q) x) y=inner ℝ x ((‖Q‖⁻¹ • Q) y)
    simp only [_root_.smul_apply,real_inner_smul_left,real_inner_smul_right]
    exact congrArg (fun t : ℝ=>‖Q‖⁻¹*t) (hQ x y)
  · intro v hv
    change 0 < inner ℝ v ((‖Q‖⁻¹ • Q) v)
    simpa only [_root_.smul_apply,real_inner_smul_right] using mul_pos hq (hpos v hv)

set_option maxHeartbeats 1000000 in
/-- The literal normalized observed references of the complete actual source
family satisfy s7:N on one constructed compact set, uniformly in the source
scale, bounded real shrink and the entire genuine binary cubic ball.
No compact-reference admission is assumed. Article: main_krylov, s7:N. -/
theorem referencePlane_normalized_reference_compact
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hn : 2≤n) (hfull : referenceAtomCount A hA g=n) (U : ℝ) (hU : 0<U) :
    ∃ ep : ℝ, 0<ep ∧ ∃ K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      (∀ z∈K, z.1.toLinearMap.IsSymmetric ∧ (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧
        ∀ i<n, CG.gradient z.1 z.2 i≠0) ∧
      ∀ ε : ℝ, 0<ε → ε<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      normalizedReference (cgOperator (referencePlaneObservedMatrix A hA g ε (scaleBinaryCubic α t)))
        (gradient (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t)) 0)∈K := by
  have hN : 2≤referenceAtomCount A hA g := by omega
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  have hg : g≠0 := by
    have hh := cg_nonstagnation A hA g 0 (by omega)
    simpa only [CG.gradient,cgRun] using hh
  obtain ⟨δ,hδ,hclose⟩ := reference_full_count_neighborhood A hA g (by omega) hfull
  obtain ⟨L,hL,hLt⟩ := planeTerminal_uniform_bounds (referencePlaneRatio A hA g)
  let J := U*‖canonicalCGStep A g 0‖*(1/2+L+‖planeOfPair (1,referencePlaneRatio A hA g)‖)
  let R := ‖(metricCoordinates A hA).toContinuousLinearMap‖^2*J
  have hJ : 0≤J := by dsimp only [J]; positivity
  have hR : 0≤R := by dsimp only [R]; positivity
  let ep := min (δ/(2*(R+1))) (1/(4*(J+1)))
  have hep : 0<ep := lt_min (div_pos hδ (by positivity)) (by positivity)
  let P := Icc (0 : ℝ) ep ×ˢ (Icc (0 : ℝ) U ×ˢ {q : Fin 4 → ℝ | (binaryFromVector q).InBall})
  let B := fun z : ℝ × ℝ × (Fin 4 → ℝ)=>
    referencePlaneObservedMatrix A hA g z.1 (scaleBinaryCubic z.2.1 (binaryFromVector z.2.2))
  let Q := fun z : ℝ × ℝ × (Fin 4 → ℝ)=>cgOperator (B z)
  have hP : IsCompact P := isCompact_Icc.prod (isCompact_Icc.prod binaryFromVector_inBall_isCompact)
  have hBP (z : ℝ × ℝ × (Fin 4 → ℝ)) (hz : z∈P) :
      (B z).PosDef ∧ ∀ hb : (B z).PosDef, referenceAtomCount (B z) hb g=n := by
    have hcan : ‖averagedDerivative (hilbertPlaneHessian (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (z.1*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g)
        (scaleBinaryCubic z.2.1 (binaryFromVector z.2.2))) 0 (z.1 • canonicalCGStep A g 0)-
        ContinuousLinearMap.id ℝ _‖≤1/2 := by
      have hb := hilbertPlaneFirstSecant_scaled_drift _ _ he hh heh (canonicalCGStep A g 0)
        (referencePlaneRatio A hA g) U z.1 z.2.1 hz.1.1 hz.2.1.1 hz.2.1.2 hz.2.2
      have hj : U*‖canonicalCGStep A g 0‖*(1/2+‖planeTerminalOperator (referencePlaneRatio A hA g) (binaryFromVector z.2.2)‖+
          ‖planeOfPair (1,referencePlaneRatio A hA g)‖)≤J := by
        dsimp only [J]; gcongr; exact (hLt _ hz.2.2).1
      have hs := (le_div_iff₀ (by positivity : 0<4*(J+1))).mp (hz.1.2.trans (min_le_right _ _))
      exact (hb.trans (mul_le_mul_of_nonneg_right hj hz.1.1)).trans (by nlinarith only [hs,hz.1.1,hδ])
    have hbP : (B z).PosDef := metricHilbertPlaneFirstSecant_posDef A hA _ _ _ _ _ _ hcan
    refine ⟨hbP,fun hb=>hclose (B z) hb ?_⟩
    have hb := metricHilbertPlaneFirstSecant_scaled_drift A hA _ _ he hh heh (canonicalCGStep A g 0)
      (referencePlaneRatio A hA g) U z.1 z.2.1 hz.1.1 hz.2.1.1 hz.2.1.2 hz.2.2
    have hj : ‖B z-A‖≤R*z.1 := by
      apply hb.trans
      have hj : U*‖canonicalCGStep A g 0‖*(1/2+‖planeTerminalOperator (referencePlaneRatio A hA g) (binaryFromVector z.2.2)‖+
          ‖planeOfPair (1,referencePlaneRatio A hA g)‖)≤J := by
        dsimp only [J]; gcongr; exact (hLt _ hz.2.2).1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (sq_nonneg _)) hz.1.1
    have hs := (le_div_iff₀ (by positivity : 0<2*(R+1))).mp (hz.1.2.trans (min_le_left _ _))
    exact hj.trans (by nlinarith only [hs,hz.1.1,hδ])
  have hQcont : Continuous Q := referencePlaneObservedOperator_continuous A hA g
  have hQne z (hz : z∈P) : Q z≠0 := by
    intro hzero
    have hp := (cgOperator_positive (B z) (hBP z hz).1).2 g hg
    change 0 < inner ℝ g (Q z g) at hp
    rw [hzero,_root_.zero_apply,inner_zero_right] at hp
    exact (lt_irrefl 0) hp
  let F := fun z : ℝ × ℝ × (Fin 4 → ℝ)=>normalizedReference (Q z) g
  have hF : ContinuousOn F P := by
    intro z hz
    exact (((hQcont.continuousAt.norm.inv₀ (norm_ne_zero_iff.mpr (hQne z hz))).smul hQcont.continuousAt).prodMk
      continuousAt_const).continuousWithinAt
  refine ⟨ep,hep,F '' P,hP.image_of_continuousOn hF,?_,?_⟩
  · rintro v ⟨z,hz,rfl⟩
    have hb := hBP z hz
    have hpre i (hi : i<n) : CG.gradient (Q z) g i≠0 :=
      cg_nonstagnation (B z) hb.1 g i (by rw [hb.2 hb.1]; exact hi)
    exact normalizedReference_nondegenerate (Q z) g hg (cgOperator_positive (B z) hb.1).1
      (cgOperator_positive (B z) hb.1).2 n hpre
  · intro ε hε heps α hα hαU t ht
    rw [referencePlaneCubicObjective_initial_gradient A hA g hN hε,normalizedReference_gradient_smul _ g ε hε]
    refine ⟨(ε,α,binaryCoefficientVector t),⟨⟨hε.le,heps.le⟩,⟨hα,hαU⟩,?_⟩,?_⟩
    · change (binaryFromVector (binaryCoefficientVector t)).InBall
      rw [binaryFromVector_coefficientVector]
      exact ht
    · simp only [F,Q,B,binaryFromVector_coefficientVector]

end
end krylov.Functions

import krylov.Functions.RFCFAsymptoticNorm
import krylov.Functions.NativeNormalizedReferences
import krylov.Functions.OwnReferenceTube

/-!
Article: main_krylov, s7:N and prop:Fcycle(i), the complete SC norm assembly.
Use: require compactness only of the actual normalized observed first-secant
and gradient pair. The auxiliary compact true-Hessian reference family is
constructed internally from genuine first-query drift and compact CG openness.
Source: actual normalized reference transport, true scalar self-concordance,
and the proved returned-gradient bound with coefficient 4*n^(3/2).
-/
namespace krylov.Functions
noncomputable section
open Matrix Set Metric krylov.Reference krylov.Nonlinear krylov.Methods krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- The actual returned RFC-F gradient has the printed self-concordant
coefficient and uniform little-o cubic error under literal s7:N alone.
The coefficient uses the true minimizer Hessian metric, in which its exact
tensor budget is two. No independent frozen compactness or nonstagnation
premise is retained. Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_normalized_selfConcordant_asymptotic_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (U : Set (EuclideanSpace ℝ (Fin (k+1))))
    (S : StandardSelfConcordantData f U) (hG₀ : gradient f 0=0)
    (hH₀ : S.hessian 0=cgOperator base) {r : ℝ} (hr : 0<r)
    (hU : ∀ z, ‖metricCoordinates base hb z‖≤r → z∈U)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) S.hessian) (closedBall 0 r))
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ, 0<η → ∃ ep : ℝ, 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖=1 →
      normalizedReference
        (rfcFunctionSearchOperator (metricCoordinates base hb) f (gradient f) S.hessian fullMemory r (ε • u) 0)
        (gradient f (ε • u))∈K →
      ‖cgOperator (metricRoot base)⁻¹
          (gradient f (rfcFPoint (metricCoordinates base hb) f (gradient f) r (ε • u) k))‖≤
        ε^3*(‖canonicalCGStep base (cgOperator base u) k‖*
          (4*(k+1)*Real.sqrt (k+1)*‖cgCanonicalError base (cgOperator base u) 0‖*
            ‖cgCanonicalError base (cgOperator base u) 1‖))+η*ε^3 := by
  have hzero : (0 : EuclideanSpace ℝ (Fin (k+1)))∈U :=
    hU 0 (by simpa only [map_zero,norm_zero] using hr.le)
  have hF z (hz : ‖metricCoordinates base hb z‖≤r) :
      HasFDerivAt f (innerSL ℝ (gradient f z)) z :=
    (S.differentiable.differentiableAt (S.open_domain.mem_nhds (hU z hz))).hasGradientAt.hasFDerivAt
  have hG z (hz : ‖metricCoordinates base hb z‖≤r) := S.gradient_derivative z (hU z hz)
  have hT := metricCoordinates_inverse_symmetric base hb
  have hHc₀ := coordinateDerivative_metric_zero base hb S.hessian hH₀
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := nativeRFC_normalized_reference_compact (metricCoordinates base hb) hT
    f (gradient f) S.hessian (cgOperator base) (cgOperator_positive base hb).2
    hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩ := nativeRFC_first_reference_drift (metricCoordinates base hb) hT
    f (gradient f) S.hessian (cgOperator base) hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  have hcount g (hg : g∈F) : referenceAtomCount base hb g=k+1 :=
    referenceAtomCount_eq_of_full_nonstagnation base hb g (fun i hi=>hpre g hg i hi)
  intro η hη
  obtain ⟨ec,hec,hbound⟩ := metricRFCFPoint_selfConcordant_asymptotic_norm base hb hk f U S hG₀ hH₀
    hr hU hLr hH F hFc hcount 1 (by norm_num) η hη
  refine ⟨min es (min ed (min ec (δ/(D+1)))),by positivity,?_⟩
  intro ε hε he u hu hn
  have hown := hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs := hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le
  have hsmall := (lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hfrozen : cgOperator base u∈F := hfreeze _ _ _ hown (hs.trans (by nlinarith only [hsmall,hε]))
  exact hbound ε hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    u hu.le hfrozen

end
end krylov.Functions

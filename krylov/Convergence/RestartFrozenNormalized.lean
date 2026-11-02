import krylov.Convergence.RestartFrozenDegree

/-!
Article: main_krylov, thm:D and s7:N, literal normalized frozen corrections.
Use: derive the entire real FC-plus-k degree family from compactness only
of the normalized observed first secant and initial gradient. The original
source produces the physical compact tube, full frozen reference family,
and every actual inverse and intermediate query enclosure.
Source: genuine normalized-reference transport and open CG nonstagnation.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Literal original normalized compactness suffices simultaneously for
all numbers of actual final frozen corrections. Article: thm:D, s7:N. -/
theorem nativeFC_frozen_corrections_normalized
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z,‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z,‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) × EuclideanSpace ℝ (Fin (k+1))))
    (hK : IsCompact K)
    (hquad : ∀ z∈K,z.1.toLinearMap.IsSymmetric ∧
      (∀ v,v≠0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i<k+1,CG.gradient z.1 z.2 i≠0) :
    ∃ ep B C : ℝ,0<ep ∧0<B ∧0<C ∧∀ ε : ℝ,0<ε → ε<ep →∀ u,‖u‖=1 →
      normalizedReference (metricFCOperator T f G H fullMemory r (ε • u) 0) (G (ε • u))∈K →
      ∀ j : ℕ,‖T (nativeFCFrozenPoints T f G r (ε • u) j)‖≤B*C^j*ε^(j+2) ∧
        ‖T (nativeFCFrozenPoints T f G r (ε • u) j)‖<r := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := metricFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF hG (k+1) K hK hquad
  obtain ⟨δ,hδ,F,hFc,hpre,hfreeze⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) P hP hq
  obtain ⟨ed,D,hed,hD,hsource⟩ := metricFCInput_bound T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF hG 1 (by norm_num)
  obtain ⟨ec,B,C,hec,hB,hC,hcycle⟩ := nativeFC_frozen_corrections_degree base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG F hFc hpre 1 (by norm_num)
  refine ⟨min es (min ed (min ec (δ/(D+1)))),B,C,by positivity,hB,hC,?_⟩
  intro ε hε he u hu hn
  have hown := hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn
  have hs := (hsource ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu.le).2 1
  have hpair : ‖(metricFCOperator T f G H fullMemory r (ε • u) 0-cgOperator base,
      ε⁻¹ • G (ε • u)-cgOperator base u)‖≤D*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨(norm_le_pi_norm (metricFCInput T f G H (cgOperator base) r ε u 1).2 ⟨0,by omega⟩).trans
      ((norm_snd_le _).trans hs),(norm_fst_le _).trans hs⟩
  have hsmall := (lt_div_iff₀ (by positivity : 0<D+1)).mp
    (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hfrozen := hfreeze _ _ _ hown (hpair.trans (by nlinarith only [hsmall,hε]))
  exact hcycle ε hε (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    u hu.le hfrozen

end
end krylov.Convergence

import krylov.Correction.RFCSOperatorTube

/-!
Article: main_krylov, thm:RFCS, uniform actual finite-prefix bounds.
Use: Choose one compact-reference tube bounding every true gradient,
direction and total evaluated step of a whole direct-operator RFC-S cycle.
Source: genuine joint prefix analyticity, finite product norms and the proved
compact full-reference value tube. No uniform trajectory bound is assumed.
-/

namespace krylov.Correction
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
variable {k : ℕ}

/-- All actual gradients, selected directions and recorded total steps of one genuine direct-operator RFC-S prefix in a fixed finite product.
Use: Apply one compact bound to every real prefix field simultaneously.
Article: main_krylov, thm:RFCS, compact actual prefix localization.
-/
def rfcsDirectPrefixValues (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1)) :=
  ((fun i : Fin (k+2) => rfcSGradient fullMemory (rfcsDirectProbe base z)
    (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i.val),
   (fun i : Fin (k+1) => rfcSDirection fullMemory (rfcsDirectProbe base z)
    (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i.val),
   (fun i : Fin (k+1) => rfcSStep fullMemory (rfcsDirectProbe base z)
    (rfcsDirectLine base z) (rfcsDirectLine base z) z.1 i.val))

/-- The entire finite product of genuine RFC-S prefix fields is jointly analytic in the actual initial gradient and all physical operator deviations.
Use: Choose a common tube before all real intermediate fields.
Article: main_krylov, thm:RFCS, compact actual prefix localization.
Proof: Combine the proved genuine prefix analyticity in the fixed finite product coordinates.
-/
theorem rfcs_direct_prefix_values_analytic (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) :
    AnalyticAt ℝ (rfcsDirectPrefixValues base) (g,0) := by
  apply AnalyticAt.prod
  · apply AnalyticAt.pi
    intro i
    exact (rfcs_direct_prefix_analytic base hb g i.val (by omega)).1
  · apply AnalyticAt.prod
    · apply AnalyticAt.pi
      intro i
      exact ((rfcs_direct_prefix_analytic base hb g (k+1) hN).2 i.val i.isLt).1
    · apply AnalyticAt.pi
      intro i
      exact ((rfcs_direct_prefix_analytic base hb g (k+1) hN).2 i.val i.isLt).2.1

/-- One genuine compact-reference tube uniformly bounds every actual intermediate RFC-S gradient, selected direction and full recorded step.
Use: Localize the real nonlinear queries after scaling by the true initial cycle size.
Article: main_krylov, thm:RFCS, compact actual prefix localization.
Proof: Apply the proved full compact-reference value tube to the actual finite prefix product, then bound each genuine field by its product norm.
-/
theorem compact_rfcs_operator_prefix_bounds (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ →
      (∀ i≤k+1, ‖rfcSGradient fullMemory (rfcsDirectProbe base (g+v,Θ))
        (rfcsDirectLine base (g+v,Θ)) (rfcsDirectLine base (g+v,Θ)) (g+v) i‖≤M) ∧
      (∀ i<k+1, ‖rfcSDirection fullMemory (rfcsDirectProbe base (g+v,Θ))
        (rfcsDirectLine base (g+v,Θ)) (rfcsDirectLine base (g+v,Θ)) (g+v) i‖≤M ∧
        ‖rfcSStep fullMemory (rfcsDirectProbe base (g+v,Θ))
        (rfcsDirectLine base (g+v,Θ)) (rfcsDirectLine base (g+v,Θ)) (g+v) i‖≤M) := by
  obtain ⟨δ,M,hδ,hM,hbound⟩ := compact_reference_value_tube (rfcsDirectPrefixValues base) K hK
    (fun g hg => rfcs_direct_prefix_values_analytic base hb g (hN g hg))
  refine ⟨δ,M,hδ,hM,?_⟩
  intro g hg v Θ hΘ
  have h := hbound g hg v Θ hΘ
  have hg' := (norm_fst_le (rfcsDirectPrefixValues base (g+v,Θ))).trans h
  have hd' := (norm_fst_le (rfcsDirectPrefixValues base (g+v,Θ)).2).trans
    ((norm_snd_le (rfcsDirectPrefixValues base (g+v,Θ))).trans h)
  have hs' := (norm_snd_le (rfcsDirectPrefixValues base (g+v,Θ)).2).trans
    ((norm_snd_le (rfcsDirectPrefixValues base (g+v,Θ))).trans h)
  refine ⟨?_,?_⟩
  · intro i hi
    exact (norm_le_pi_norm _ (⟨i,by omega⟩ : Fin (k+2))).trans hg'
  · intro i hi
    exact ⟨(norm_le_pi_norm _ (⟨i,hi⟩ : Fin (k+1))).trans hd',
      (norm_le_pi_norm _ (⟨i,hi⟩ : Fin (k+1))).trans hs'⟩

end
end krylov.Correction

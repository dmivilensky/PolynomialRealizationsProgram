import krylov.Correction.RFCSOperatorTube
import krylov.Stability.CompactFirstOrder

/-!
Article: main_krylov, thm:RFCS, genuine fixed-reference only-last-probe tube.
Use: Keep the original reference CG terminal step fixed while the actual
initial gradient and every physical operator vary in one compact tube.
Source: the proved full direct-operator quadratic remainder and genuine
compact first-order regularity of the actual CG reference step.
-/

namespace krylov.Correction
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Stability
variable {k : ℕ}

/-- The genuine RFC-S terminal output has a uniform quadratic remainder about the last true probe mismatch applied to the original fixed-reference CG step, including simultaneous actual initial-gradient drift.
Use: Multiply by the actual cycle scale to obtain the genuine nonlinear cubic remainder with the original quadratic reference.
Article: main_krylov, thm:RFCS, actual compact fixed-reference source expansion.
Proof: The existing actual operator tube gives the remainder with the slightly shifted reference step. Its genuine compact first-order variation is multiplied by the actual source probe mismatch, so replacing it with the original fixed-reference step costs only quadratic source order.
-/
theorem compact_rfcs_fixed_reference_quadratic_tube (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ g∈K, ∀ v : EuclideanSpace ℝ (Fin (k+1)),
      ∀ Θ : RFCSOperatorParameters (k+1), ‖(v,Θ)‖≤δ →
      ‖rfcsDirectOutput base (g+v,Θ)-
        (rfcsDirectLine base (g+v,Θ) k-rfcsDirectProbe base (g+v,Θ) k)
          (referenceStep (cgOperator base) g k)‖≤C*‖(v,Θ)‖^2 := by
  obtain ⟨δ₀,C,hδ₀,hC,hbound⟩ := compact_rfcs_operator_quadratic_tube base hb K hK hN hk
  let f := fun z : EuclideanSpace ℝ (Fin (k+1)) × RFCSOperatorParameters (k+1) => rfcsDirectReferenceStep base z.1
  have hf g (hg : g∈K) : AnalyticAt ℝ f (g,0) :=
    (rfcsDirectReferenceStep_analytic base hb g (hN g hg)).comp
      (f := Prod.fst) (x := (g,(0 : RFCSOperatorParameters (k+1)))) analyticAt_fst
  obtain ⟨δ₁,M,hδ₁,hM,hstep⟩ := compact_reference_full_first_order f K hK hf
  refine ⟨min δ₀ δ₁,C+M,lt_min hδ₀ hδ₁,add_pos hC hM,?_⟩
  intro g hg v Θ hΘ
  have hout := hbound g hg v Θ (hΘ.trans (min_le_left _ _))
  have hs := hstep g hg v Θ (hΘ.trans (min_le_right _ _))
  simp only [f,rfcsDirectReferenceStep_eq_cg base hb] at hs
  let P := rfcsDirectLine base (g+v,Θ) k-rfcsDirectProbe base (g+v,Θ) k
  have hP : P=Θ.2 ⟨k,Nat.lt_succ_self k⟩ := by
    dsimp only [P,rfcsDirectProbe]
    rw [sub_sub_cancel]
    simp only [rfcsOperatorAt,dite_eq_left (Nat.lt_succ_self k)]
  have hp : ‖P‖≤‖(v,Θ)‖ := by
    rw [hP]
    exact (norm_le_pi_norm Θ.2 ⟨k,Nat.lt_succ_self k⟩).trans
      ((norm_snd_le Θ).trans (norm_snd_le (v,Θ)))
  have hmove : ‖P (referenceStep (cgOperator base) (g+v) k-referenceStep (cgOperator base) g k)‖≤M*‖(v,Θ)‖^2 := by
    calc
      _ ≤ ‖P‖*‖referenceStep (cgOperator base) (g+v) k-referenceStep (cgOperator base) g k‖ := P.le_opNorm _
      _ ≤ ‖(v,Θ)‖*(M*‖(v,Θ)‖) := mul_le_mul hp hs (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have he : rfcsDirectOutput base (g+v,Θ)-P (referenceStep (cgOperator base) g k)=
      (rfcsDirectOutput base (g+v,Θ)-P (referenceStep (cgOperator base) (g+v) k))+
      P (referenceStep (cgOperator base) (g+v) k-referenceStep (cgOperator base) g k) := by
    rw [map_sub]
    abel
  change ‖rfcsDirectOutput base (g+v,Θ)-P (referenceStep (cgOperator base) g k)‖≤_
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hout hmove).trans_eq (by ring))

end
end krylov.Correction

import krylov.Functions.ValueModelCoordinates
import krylov.Functions.NativeRFCTrajectory

/-!
Article: main_krylov, prop:Fcycle(i), true retained RFC-F segments.
Use: read the actual last value-corrected model on its real old total steps
and newest searched segment. All retained endpoints have the original
compact native bounds, and all these segments shadow their genuine CG
reference segments to second order.
Source: the proved ordinary native RFC prefix and finite vector subtraction;
no segment bounds or reference trajectories are algorithm inputs.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual retained value-model segment has both genuinely evaluated
endpoints in the proved native query ball.
Article: main_krylov, prop:Fcycle, actual scalar-oracle enclosure. -/
theorem NativeRFCPrefixBounds.rfcF_segments_local
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C (k+1)) :
    ∀ i : Fin (k+1), ‖rfcFAnchors T f G r (ε • u) k i‖≤M*ε ∧
      ‖rfcFAnchors T f G r (ε • u) k i+rfcFSteps T f G r (ε • u) k i‖≤M*ε := by
  intro i
  refine ⟨(hp.1 i.val (by omega)).1,?_⟩
  by_cases hi : i.val<k
  · rw [rfcFSteps_old_endpoint T f G r (ε • u) k i hi]
    exact (hp.1 (i.val+1) (by omega)).1
  · have hiv : i.val=k := by omega
    have hie : i=Fin.last k := Fin.ext hiv
    rw [hie,rfcFSteps_last_endpoint]
    exact (hp.2 k (by omega)).2.2.1

/-- Every actual retained value-model anchor has its true quadratic-reference
location with the derived native second-order error.
Article: main_krylov, prop:Fcycle, actual anchor dictionary. -/
theorem NativeRFCPrefixBounds.rfcF_reference_anchors
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C (k+1)) :
    ∀ i : Fin (k+1), ‖rfcFAnchors T f G r (ε • u) k i-
      ε • fcQuadraticReferencePoint Q u i.val‖≤(i.val:ℝ)*C*ε^2 :=
  fun i=>hp.reference_points T f G H Q r u ε M D C (k+1) i.val (by omega)

/-- The actual newest searched endpoint has the true final reference node,
including the ordinary prefix's actual correction displacements.
Article: main_krylov, prop:Fcycle, genuine terminal anchor. -/
theorem NativeRFCPrefixBounds.rfcF_reference_anchor
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C (k+1)) :
    ‖rfcFAnchor T f G r (ε • u) k-ε • fcQuadraticReferencePoint Q u (k+1)‖≤
      ((k:ℝ)+2)*C*ε^2 :=
  hp.reference_search_points T f G H Q r u ε M D C (k+1) k (by omega)

/-- Each real retained segment has the actual reference CG step as its first term.
Article: main_krylov, prop:Fcycle. The same bound covers old total corrected
steps and the newest true searched segment. -/
theorem NativeRFCPrefixBounds.rfcF_reference_steps
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C (k+1)) (hC : 0≤C) :
    ∀ i : Fin (k+1), ‖rfcFSteps T f G r (ε • u) k i-
      ε • referenceStep Q (Q u) i.val‖≤(2*(k:ℝ)+2)*C*ε^2 := by
  intro i
  have ha := hp.rfcF_reference_anchors T f G H Q r u ε M D C k i
  have hstep : ε • referenceStep Q (Q u) i.val=
      ε • fcQuadraticReferencePoint Q u (i.val+1)-ε • fcQuadraticReferencePoint Q u i.val := by
    rw [←smul_sub,fcQuadraticReferencePoint_step]
  rw [hstep]
  have he : rfcFSteps T f G r (ε • u) k i-
      (ε • fcQuadraticReferencePoint Q u (i.val+1)-ε • fcQuadraticReferencePoint Q u i.val)=
      (rfcFAnchors T f G r (ε • u) k i+rfcFSteps T f G r (ε • u) k i-
        ε • fcQuadraticReferencePoint Q u (i.val+1))-
      (rfcFAnchors T f G r (ε • u) k i-ε • fcQuadraticReferencePoint Q u i.val) := by abel
  rw [he]
  by_cases hi : i.val<k
  · have hb := hp.reference_points T f G H Q r u ε M D C (k+1) (i.val+1) (by omega)
    rw [←rfcFSteps_old_endpoint T f G r (ε • u) k i hi] at hb
    have hik : (i.val:ℝ)≤(k:ℝ) := by exact_mod_cast hi.le
    exact (norm_sub_le _ _).trans ((add_le_add hb ha).trans (by push_cast; nlinarith [mul_le_mul_of_nonneg_right hik (mul_nonneg hC (sq_nonneg ε))]))
  · have hiv : i.val=k := by omega
    have hie : i=Fin.last k := Fin.ext hiv
    have hb := hp.rfcF_reference_anchor T f G H Q r u ε M D C k
    rw [hiv,show rfcFAnchors T f G r (ε • u) k i+rfcFSteps T f G r (ε • u) k i=
      rfcFAnchor T f G r (ε • u) k by rw [hie,rfcFSteps_last_endpoint]]
    exact (norm_sub_le _ _).trans ((add_le_add hb (by simpa only [hiv] using ha)).trans_eq (by ring))

/-- Actual retained value-model segments have the genuine small-step bound
inherited from their two actual evaluated endpoints.
Article: main_krylov, prop:Fcycle, before evaluating the final changed query. -/
theorem NativeRFCPrefixBounds.rfcF_steps_local
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (r : ℝ) (u : E) (ε M D C : ℝ) (k : ℕ)
    (hp : NativeRFCPrefixBounds T f G H Q r u ε M D C (k+1)) :
    ∀ i : Fin (k+1), ‖rfcFSteps T f G r (ε • u) k i‖≤2*M*ε := by
  intro i
  obtain ⟨ha,hb⟩ := hp.rfcF_segments_local T f G H Q r u ε M D C k i
  have he : rfcFSteps T f G r (ε • u) k i=
      (rfcFAnchors T f G r (ε • u) k i+rfcFSteps T f G r (ε • u) k i)-
        rfcFAnchors T f G r (ε • u) k i := by abel
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hb ha).trans_eq (by ring))

end
end krylov.Functions

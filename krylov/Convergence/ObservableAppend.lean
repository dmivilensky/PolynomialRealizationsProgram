import krylov.Convergence.ObservableRFCState

/-!
Article: main_krylov, apG:Dunif, actual newest-first invariant update.
Use: transport proved analytic step bounds through the literal recorded
gradient and pair extraction. Source: the actual observation semantics;
the accepted-step estimates are supplied by the separate source proof.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Appending a real iteration inserts its actual step at the first
canonical primal coordinate. Article: apG:Dunif. -/
theorem observablePrimal_append (T : E ≃L[ℝ] E) (B : History E) (rec : IterationRecord E) :
    observablePrimal T ⟨B.initial,rec::B.records⟩=
      Fin.cons (T rec.step) (observablePrimal T B) := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

/-- The inserted dual image is the true newly observed gradient
difference. Article: apG:Dunif. -/
theorem observableDual_append (T : E ≃L[ℝ] E) (B : History E) (rec : IterationRecord E) :
    observableDual T ⟨B.initial,rec::B.records⟩=
      Fin.cons (T.symm (rec.gradient-B.gradient)) (observableDual T B) := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

/-- Genuine new observations and proved analytic step estimates update
the entire real RFC invariant, including all old/new angular pairs.
This is an internal induction lemma, not a hypothesis of the scalar
source theorem. Article: main_krylov, apG:Dunif. -/
theorem ObservableRFCInvariant.append {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {x₀ : E} {N : ℕ} {epsilon bar : ℝ} {B : History E}
    (I : ObservableRFCInvariant T f G x₀ N epsilon bar B) (rec : IterationRecord E)
    (hg : rec.gradient=G (x₀+(History.mk B.initial (rec::B.records)).displacement))
    (hx : ‖T (x₀+(History.mk B.initial (rec::B.records)).displacement)‖≤2*‖T x₀‖)
    (hv : f (x₀+(History.mk B.initial (rec::B.records)).displacement)≤f x₀)
    (hs : T rec.step≠0)
    (hy : ‖T.symm (rec.gradient-B.gradient)-T rec.step‖≤(2*epsilon)*‖T rec.step‖)
    (ha : ∀ i,|inner ℝ (unitWindow (observablePrimal T B) i)
      (‖T rec.step‖⁻¹ • T rec.step)|≤2*epsilon+3*bar)
    (hr : ‖projectedResidual (unitWindow (Fin.cons (T rec.step) (observablePrimal T B)))
      (T.symm rec.gradient)‖≤observableRFCResidualBudget N epsilon ‖T x₀‖) :
    ObservableRFCInvariant T f G x₀ N epsilon bar ⟨B.initial,rec::B.records⟩ := by
  refine ⟨hg,hx,hv,?_,?_,?_,?_⟩
  · rw [observablePrimal_append]
    intro i
    exact Fin.cases hs I.steps i
  · rw [observablePrimal_append,observableDual_append]
    intro i
    exact Fin.cases hy I.pairs i
  · rw [observablePrimal_append]
    intro i
    refine Fin.cases ?_ (fun a=>?_) i
    · intro j
      refine Fin.cases ?_ (fun b=>?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        change |inner ℝ (‖T rec.step‖⁻¹ • T rec.step)
          (unitWindow (observablePrimal T B) b)|≤_
        rw [real_inner_comm]
        exact ha b
    · intro j
      refine Fin.cases ?_ (fun b=>?_) j
      · intro _
        exact ha a
      · intro hij
        exact I.angles a b (fun he=>hij (congrArg Fin.succ he))
  · rw [observablePrimal_append]
    exact hr

end
end krylov.Convergence

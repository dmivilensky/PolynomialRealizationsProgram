import krylov.Methods.CorrectionProgram
import krylov.Methods.InformationSpan

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine appended correction protocols.
Use: append a real final observed-gradient correction after any actual
finite adaptive correction tree, preserving true observations, physical
movement, subspace information and quadratic zero-query consistency.
Source: genuine nonanticipating correction-tree execution and the
actual observed current-gradient continuation convention.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine adaptive correction tree followed by a real terminal protocol using its actual returned gradient.
Use: A genuine adaptive correction tree followed by a real terminal protocol using its actual returned gradient.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine appended correction protocols.
Proof: Preserve each true query and attach the actual final continuation only after its real preceding tree terminates. -/
def CorrectionTree.follow (p : CorrectionTree E) (finish : E → CorrectionTree E) (g : E) : CorrectionTree E :=
  match p with
  | .done => finish g
  | .query u next => .query u (fun gnew => (next gnew).follow finish gnew)

/-- Executing an actual followed correction tree adds the two genuine movements, returns the true final gradient and concatenates the actual query traces.
Use: Executing an actual followed correction tree adds the two genuine movements, returns the true final gradient and concatenates the actual query traces.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine appended correction protocols.
Proof: Induct on the real first correction tree, retaining its genuine returned gradient before starting the actual appended protocol. -/
theorem CorrectionTree.run_follow (p : CorrectionTree E) (finish : E → CorrectionTree E)
    (B : E →L[ℝ] E) (g : E) :
    let r := runCorrections p B g
    let s := runCorrections (finish r.gradient) B r.gradient
    (runCorrections (p.follow finish g) B g).movement=r.movement+s.movement ∧
    (runCorrections (p.follow finish g) B g).gradient=s.gradient ∧
    (runCorrections (p.follow finish g) B g).trace=r.trace++s.trace := by
  induction p generalizing g with
  | done => exact ⟨(zero_add _).symm,rfl,rfl⟩
  | query u next ih =>
    obtain ⟨hm,hg,ht⟩ := ih (g+B u) (g+B u)
    dsimp only [CorrectionTree.follow,runCorrections]
    exact ⟨by rw [hm];abel,hg,by rw [ht,List.cons_append]⟩

/-- Appending any genuine same-subspace terminal correction preserves actual all-branch correction-span admissibility.
Use: Appending any genuine same-subspace terminal correction preserves actual all-branch correction-span admissibility.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine appended correction protocols.
Proof: Induct through the true first tree and use the real terminal subspace restriction for every possible actual returned gradient. -/
theorem CorrectionTree.follow_inSubspace (K : Submodule ℝ E) (p : CorrectionTree E)
    (finish : E → CorrectionTree E) (g : E) (hp : p.InSubspace K)
    (hf : ∀ v, (finish v).InSubspace K) : (p.follow finish g).InSubspace K := by
  induction p generalizing g with
  | done => exact hf g
  | query u next ih => exact ⟨hp.1,fun v => ih v v (hp.2 v)⟩

/-- Appending a genuine zero correction phase to an actual quadratic zero-query transcript preserves real quadratic zero-correction consistency.
Use: Appending a genuine zero correction phase to an actual quadratic zero-query transcript preserves real quadratic zero-correction consistency.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine appended correction protocols.
Proof: Every actual preceding zero query returns the same true gradient; the genuine terminal phase therefore receives its real unchanged input. -/
theorem CorrectionTree.zeroCorrections_follow (p : CorrectionTree E) (finish : E → CorrectionTree E)
    (B : E →L[ℝ] E) (g : E) (hp : ZeroCorrections p B g)
    (hf : ZeroCorrections (finish g) B g) : ZeroCorrections (p.follow finish g) B g := by
  -- Actual zero queries preserve the genuine current gradient before the real appended correction begins.
  induction p generalizing g with
  | done => exact hf
  | query u next ih =>
    obtain ⟨hu,hnext⟩ := hp
    subst u
    simp only [map_zero,add_zero] at hnext
    change 0=0 ∧ ZeroCorrections ((next (g+B 0)).follow finish (g+B 0)) B (g+B 0)
    simp only [map_zero,add_zero]
    exact ⟨trivial,ih g g hnext hf⟩

end
end krylov.Methods

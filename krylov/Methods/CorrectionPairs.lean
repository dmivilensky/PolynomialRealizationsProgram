import krylov.Methods.StaticTermination
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: main_krylov, lem:projected-residual and apD:eq:pairs.
Use: identify the actual recorded secant after a finite correction phase and
its genuine second-order discrepancy from the line operator's image.
Source: exact telescoping of the existing observed-gradient oracle execution.
-/

namespace krylov.Methods
noncomputable section
open Filter Asymptotics Topology krylov.Reference krylov.LinearAlgebra
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The correction movement is precisely the sum of its actually recorded query displacements.
Use: recorded-pair error formulas count the real correction queries.
Article: main_krylov, apD:eq:pairs, sum over corrections.
Proof: the executed tree prepends its real query and adds its real movement at every node. -/
theorem runCorrections_movement_trace (q : CorrectionTree E) (B : E →L[ℝ] E) (g : E) :
    (runCorrections q B g).movement=((runCorrections q B g).trace.map Prod.fst).sum := by
  induction q generalizing g with
  | done => rfl
  | query u next ih =>
    change u+(runCorrections (next (g+B u)) B (g+B u)).movement=
      u+((runCorrections (next (g+B u)) B (g+B u)).trace.map Prod.fst).sum
    rw [ih]

/-- A genuine line followed by any finite adaptive correction phase has the exact recorded-pair defect.
Use: the source pair identity holds for all implemented RFC correction counts and gates.
Article: main_krylov, apD:eq:pairs, y=As+(B−A)χ.
Proof: use the true correction gradient balance and subtract the line operator applied to the total movement. -/
theorem correction_pair_identity (A B : E →L[ℝ] E) (g line : E) (q : CorrectionTree E) :
    (runCorrections q B (g+A line)).gradient-g=
      A (line+(runCorrections q B (g+A line)).movement)+
        (B-A) (runCorrections q B (g+A line)).movement := by
  rw [runCorrections_gradient, map_add, _root_.sub_apply]
  abel

/-- The genuine recorded-pair defect is the sum of the actual correction-query mismatches.
Use: specializes the printed multi-correction pair formula to the implemented fixed correction operator.
Article: main_krylov, apD:eq:pairs.
Proof: the actual correction movement equals its recorded query sum, and the operator mismatch is linear. -/
theorem correction_pair_trace_identity (A B : E →L[ℝ] E) (g line : E) (q : CorrectionTree E) :
    (runCorrections q B (g+A line)).gradient-g=
      A (line+(runCorrections q B (g+A line)).movement)+
        ((runCorrections q B (g+A line)).trace.map (fun pair => (B-A) pair.1)).sum := by
  rw [correction_pair_identity, runCorrections_movement_trace, map_list_sum, List.map_map]
  rfl

/-- The newest actual pair recorded by any implemented probed method has the exact correction defect.
Use: no surrogate trajectory or unobserved model image is substituted for the executed secant.
Article: main_krylov, apD:eq:pairs.
Proof: unfold the actual history update and apply the proved line/correction balance. -/
theorem methodAdvance_pair_identity (m : ProbedMethod E) (A B : E →L[ℝ] E) (H : History E) :
    let d := m.direction H
    let z := A d
    let r := runCorrections (m.correction H z) B (searchedGradient H.gradient d z)
    (methodAdvance m A B H).pairs=
      (lineLength H.gradient d z • d+r.movement,
        A (lineLength H.gradient d z • d+r.movement)+(B-A) r.movement)::H.pairs := by
  -- The newest pair is extracted from the real new record and its actual preceding gradient.
  dsimp only
  change (_, (runCorrections _ B _).gradient-H.gradient)::_=_
  congr 2
  have he := correction_pair_identity A B H.gradient
    (lineLength H.gradient (m.direction H) (A (m.direction H)) • m.direction H)
    (m.correction H (A (m.direction H)))
  simpa only [map_smul, searchedGradient] using he

/-- First-order correction movements and first-order operator mismatches give a quadratic actual pair defect.
Use: apply directly to the correction movement returned by the executed RFC tree.
Article: main_krylov, apD:eq:pairs, y=As+O(ω²).
Proof: the exact pair identity identifies its defect with the true mismatch action;
the existing operator-action estimate multiplies the two first-order bounds. -/
theorem correction_pair_defect_order {α : Type*} {f : Filter α}
    (A B : α → E →L[ℝ] E) (g line : α → E) (q : α → CorrectionTree E) (ω : α → ℝ)
    (hBA : (fun x => B x-A x) =O[f] ω)
    (hχ : (fun x => (runCorrections (q x) (B x) (g x+A x (line x))).movement) =O[f] ω) :
    (fun x => (runCorrections (q x) (B x) (g x+A x (line x))).gradient-g x-
      A x (line x+(runCorrections (q x) (B x) (g x+A x (line x))).movement)) =O[f]
        (fun x => ω x^2) := by
  have ht := operator_action_order (fun x => B x-A x)
    (fun x => (runCorrections (q x) (B x) (g x+A x (line x))).movement) ω ω hBA hχ
  apply ht.congr' (Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
  · rw [correction_pair_identity]
    abel
  · exact (pow_two _).symm

end
end krylov.Methods

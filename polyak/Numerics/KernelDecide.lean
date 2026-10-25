import Lean.Elab.Tactic
import Lean.Meta.AppBuilder

/-!
An ordinary kernel proof by reduction of a decidable proposition. The tactic
constructs `of_decide_eq_true` directly, so the elaborator does not first repeat
a large exact computation while inferring its implicit proposition argument.
The declaration is still checked by Lean's kernel; there is no native evaluator,
additional axiom, or change of resource options.
-/

open Lean Meta Elab Tactic

/-- Close a decidable proposition using the standard reduction proof, checked by the kernel. -/
elab "kernel_decide" : tactic => withMainContext do
  let goal ← getMainGoal
  let type ← goal.getType
  let inst ← synthInstance (mkApp (mkConst ``Decidable) type)
  let refl ← mkEqRefl (mkConst ``Bool.true)
  goal.assign (mkApp3 (mkConst ``of_decide_eq_true) type inst refl)
  replaceMainGoal []

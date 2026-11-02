import krylov.OneGradient.TwoModelRisk
import krylov.Methods.InformationSpan
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), genuine arbitrary-policy two-query fibres.
Use: construct the actual hidden-model indistinguishability on complete
executed one-gradient histories, without CG consistency or smoothness.
Source: literal one-gradient record recursion and true equal queried actions.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true two-query prefix with known first operator and prescribed
second segment; no future model enters either original decision function.
Use: genuine known-base hidden-entry adversarial executions.
Article: main_krylov, thm:local(c), actual two-query operators. -/
def twoQueryOperators (Q C : E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E := if k=0 then Q else C

/-- An actual one-gradient step records exactly the same complete data
whenever its two real queried operator actions agree.
Use: hidden-entry indistinguishability is about genuine full histories,
including actual steps and every returned gradient.
Article: main_krylov, thm:local(c), true data preservation.
Proof: the actual query is already chosen from the common history;
the only new operator-dependent record field is its returned action. -/
theorem oneGradientAdvance_equal_action (m : OneGradientMethod E) (A B : E →L[ℝ] E)
    (H : History E) (he : A (m.step H)=B (m.step H)) :
    oneGradientAdvance m A H=oneGradientAdvance m B H := by
  dsimp only [oneGradientAdvance]
  rw [he]

/-- Every actual two-query policy has the same first complete record
for all choices of the unknown second segment operator.
Use: the true second query is common to the whole original hidden fibre.
Article: main_krylov, thm:local(c), genuine first-prefix causality.
Proof: the real first evaluation uses only the prescribed known operator. -/
theorem twoQuery_first_history (m : OneGradientMethod E) (Q C : E →L[ℝ] E) (g : E) :
    oneGradientRun m (twoQueryOperators Q C) g 1=oneGradientRun m (fun _ => Q) g 1 := by
  rfl

/-- Two actual second-segment operators agreeing on the true second
query produce exactly the same entire two-query executed history for
an arbitrary original data-only method.
Use: every unknown hidden entry forces one common actual output, with
no policy consistency, continuity, boundedness or nonzero-query premise.
Article: main_krylov, thm:local(c), full hidden-fibre indistinguishability.
Proof: the genuine first histories coincide. The actual second decision
is therefore identical, and equal queried actions give equal real records. -/
theorem twoQuery_equal_histories (m : OneGradientMethod E) (Q A B : E →L[ℝ] E) (g : E)
    (he : A (m.step (oneGradientRun m (fun _ => Q) g 1))=
      B (m.step (oneGradientRun m (fun _ => Q) g 1))) :
    oneGradientRun m (twoQueryOperators Q A) g 2=oneGradientRun m (twoQueryOperators Q B) g 2 := by
  change oneGradientAdvance m (twoQueryOperators Q A 1) (oneGradientRun m (twoQueryOperators Q A) g 1)=
    oneGradientAdvance m (twoQueryOperators Q B 1) (oneGradientRun m (twoQueryOperators Q B) g 1)
  rw [twoQuery_first_history,twoQuery_first_history]
  simp only [twoQueryOperators,ite_eq_right (by decide : (1 : ℕ)≠0)]
  exact oneGradientAdvance_equal_action m A B _ he

/-- Actual opposite hidden completions annihilating the true last query
have the same complete executed history, hence the same arbitrary original
output, even when the method's real second query is zero.
Use: the finite two-model robust lower bound applies to actual M1 policies.
Article: main_krylov, thm:local(c), actual hidden-entry pair.
Proof: both true hidden actions vanish on the already chosen second query;
apply the genuine complete-history action dictionary. -/
theorem twoQuery_hidden_histories (m : OneGradientMethod E) (Q C D : E →L[ℝ] E) (g : E)
    (hD : D (m.step (oneGradientRun m (fun _ => Q) g 1))=0) :
    oneGradientRun m (twoQueryOperators Q (C+D)) g 2=oneGradientRun m (twoQueryOperators Q C) g 2 ∧
    oneGradientRun m (twoQueryOperators Q (C-D)) g 2=oneGradientRun m (twoQueryOperators Q C) g 2 := by
  constructor
  · apply twoQuery_equal_histories
    simp only [_root_.add_apply,hD,add_zero]
  · apply twoQuery_equal_histories
    simp only [_root_.sub_apply,hD,sub_zero]

/-- The actual two hidden executions have exactly the common centre
gradient and their genuine arbitrary output residuals, with an independent
last operator perturbation that has never entered an evaluated record.
Use: the original two-model risk is tied to actual one-gradient semantics.
Article: main_krylov, thm:local(c), genuine terminal residual dictionary.
Proof: the proved real complete histories coincide; expand only the true
unevaluated output-gradient definition at that same observed history. -/
theorem twoQuery_hidden_outputs (m : OneGradientMethod E) (Q C D F : E →L[ℝ] E) (g : E)
    (hD : D (m.step (oneGradientRun m (fun _ => Q) g 1))=0) :
    let H := oneGradientRun m (twoQueryOperators Q C) g 2
    m.outputGradient (C+D+F) (oneGradientRun m (twoQueryOperators Q (C+D)) g 2)=H.gradient+(C+D) (m.output H)+F (m.output H) ∧
    m.outputGradient (C-D+F) (oneGradientRun m (twoQueryOperators Q (C-D)) g 2)=H.gradient+(C-D) (m.output H)+F (m.output H) := by
  have hh := twoQuery_hidden_histories m Q C D g hD
  dsimp only
  rw [hh.1,hh.2,OneGradientMethod.outputGradient,OneGradientMethod.outputGradient]
  constructor <;> simp only [_root_.add_apply,add_assoc]

end
end krylov.OneGradient

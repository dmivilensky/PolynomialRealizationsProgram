import krylov.Methods.OneGradient
import krylov.Information.PhysicalReplay
set_option autoImplicit false
/-!
Article: main_krylov, thm:local, actual source/native operator dictionary.
Use: apply genuine native trajectory expansions to the full original
physical source class, retaining its independent unevaluated output form.
Source: exact physical scenario probes, source output operator and the
actual finite one-gradient executor; no trajectory comparison is assumed.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant krylov.Information
variable {p : ℕ}

/-- The genuine source query matrices, extended at the output slot by
the real independent unevaluated source output operator.
Use: one native varying-operator family represents exactly a source cycle.
Article: main_krylov, thm:local, true source operator extension. -/
def oneGradientScenarioMatrices (S : Scenario p) (N k : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  if k≤N then S.probe k else S.lastOperator N

/-- Every actual query reads exactly its original physical source probe.
Use: no output operator is exposed to any native trial or query decision.
Article: main_krylov, thm:local, real query operator dictionary.
Proof: every actual query index is at most the final probe index. -/
theorem oneGradientScenarioMatrices_probe (S : Scenario p) (N k : ℕ) (hk : k≤N) :
    oneGradientScenarioMatrices S N k=S.probe k := by
  rw [oneGradientScenarioMatrices,ite_eq_left hk]

/-- The genuine extension's output slot is precisely the independent
original source output matrix.
Use: the native semantic output is the source's true unevaluated gradient.
Article: main_krylov, thm:local, genuine final output operator.
Proof: the output slot is strictly after the last actual probe. -/
theorem oneGradientScenarioMatrices_output (S : Scenario p) (N : ℕ) :
    oneGradientScenarioMatrices S N (N+1)=S.lastOperator N := by
  rw [oneGradientScenarioMatrices,ite_eq_right (by omega)]

/-- Every real native history on the true extended matrices equals
its original source-oracle history through every actual query prefix.
Use: source scenarios and native expansion theorems have exactly the
same observations and output decisions, without regularity assumptions.
Article: main_krylov, thm:local, complete original source history equality.
Proof: finite induction uses the exact same real probe at every actual
query. The actual one-gradient advance therefore returns the same record. -/
theorem oneGradientScenarioMatrices_histories (S : Scenario p) (N : ℕ)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin p))) (g : EuclideanSpace ℝ (Fin p)) :
    ∀ k≤N+1,oneGradientRun m (fun j => cgOperator (oneGradientScenarioMatrices S N j)) g k=
      oneGradientRun m S.probeOracle g k := by
  intro k
  induction k with
  | zero => intro _;rfl
  | succ k ih =>
    intro hk
    change oneGradientAdvance m (cgOperator (oneGradientScenarioMatrices S N k))
      (oneGradientRun m (fun j => cgOperator (oneGradientScenarioMatrices S N j)) g k)=_
    rw [ih (by omega),oneGradientScenarioMatrices_probe S N k (by omega)]
    rfl

/-- Every true query increment in the native extension is exactly its
original physical source increment, before any change of metric.
Use: original per-increment budgets apply to native actual differences.
Article: main_krylov, thm:local, physical increment dictionary.
Proof: both actual endpoints are real probes; the true source probe
recursion adds precisely its next original increment. -/
theorem oneGradientScenarioMatrices_increment (S : Scenario p) (N k : ℕ) (hk : k<N) :
    oneGradientScenarioMatrices S N (k+1)-oneGradientScenarioMatrices S N k=S.increment k := by
  rw [oneGradientScenarioMatrices_probe S N (k+1) (by omega),
    oneGradientScenarioMatrices_probe S N k hk.le,Scenario.probe_succ,add_sub_cancel_left]

/-- The true final increment in the native extension is exactly the
original independent unevaluated output defect.
Use: source output budgets remain independent of every measured query.
Article: main_krylov, thm:local, physical output increment dictionary.
Proof: the source output operator adds its actual independent terminal form. -/
theorem oneGradientScenarioMatrices_terminal (S : Scenario p) (N : ℕ) :
    oneGradientScenarioMatrices S N (N+1)-oneGradientScenarioMatrices S N N=S.terminal := by
  rw [oneGradientScenarioMatrices_output,oneGradientScenarioMatrices_probe S N N le_rfl]
  exact add_sub_cancel_left _ _

end
end krylov.OneGradient

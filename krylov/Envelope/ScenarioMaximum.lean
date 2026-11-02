import krylov.Envelope.ScenarioBudgets
import krylov.Envelope.ScenarioRFC

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Use: define the genuine worst transverse response and actual common-tilt
selection value on the real symmetric canonical budgets, and derive true
maximum attainment and zero-budget nonnegativity from compactness.
Source: standard extreme value theorem on the proved actual compact
scenario budget sets and genuine continuous linear first-variation maps.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- The genuine worst canonical transverse first variation over the actual full finite source scenario budget set.
Use: The genuine worst canonical transverse first variation over the actual full finite source scenario budget set.
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Proof: Take the true real supremum of the actual finite-scenario variation norms. -/
def worstTransverse (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (ω : Fin (N-1) → ℝ≥0) : ℝ :=
  sSup ((fun Θ => ‖scenarioVariation m base g N Θ‖) '' scenarioBudget N ω)

/-- The genuine worst finite source scenario variation norm is an actually attained maximum.
Use: The genuine worst finite source scenario variation norm is an actually attained maximum.
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Proof: The real scenario budget set is compact and contains the true zero scenario; its genuine continuous linear variation has a compact nonempty norm image. -/
theorem worstTransverse_attained (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest ((fun Θ => ‖scenarioVariation m base g N Θ‖) '' scenarioBudget N ω) (worstTransverse m base g N ω) := by
  -- Use the genuine compact nonempty norm image to derive the actual maximum and identify its true real supremum.
  have hc := (scenarioBudget_compact (n := n) ω).image (scenarioVariation m base g N).continuous.norm
  have hn : ((fun Θ => ‖scenarioVariation m base g N Θ‖) '' scenarioBudget N ω).Nonempty :=
    ⟨_,0,scenarioBudget_zero_mem ω,rfl⟩
  obtain ⟨V,hV⟩ := hc.exists_isGreatest hn
  change IsGreatest _ (sSup _)
  rw [hV.csSup_eq]
  exact hV

/-- The true common-tilt selection value on the genuine actual canonical increment budget profile.
Use: The true common-tilt selection value on the genuine actual canonical increment budget profile.
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Proof: Take the real supremum of the actual continuous common-tilt map norms on the true increment budget. -/
def selectionValue (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) : ℝ :=
  sSup ((fun E => ‖canonicalTiltLinear base g N E‖) '' incrementBudget N ω)

/-- The actual genuine common-tilt selection value is a truly attained increment-scenario maximum.
Use: The actual genuine common-tilt selection value is a truly attained increment-scenario maximum.
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Proof: The real increment budget is compact and nonempty, and the genuine common-tilt operator is actually continuous. -/
theorem selectionValue_attained (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) :
    IsGreatest ((fun E => ‖canonicalTiltLinear base g N E‖) '' incrementBudget N ω) (selectionValue base g N ω) := by
  have hc := (incrementBudget_compact (n := n) ω).image (canonicalTiltLinear base g N).continuous.norm
  -- The actual zero increment profile supplies genuine nonemptiness even when all true budgets vanish.
  have hzero : (0 : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ)∈incrementBudget N ω :=
    (scenarioBudget_zero_mem (n := n) ω).1
  have hn : ((fun E => ‖canonicalTiltLinear base g N E‖) '' incrementBudget N ω).Nonempty := ⟨_,0,hzero,rfl⟩
  obtain ⟨V,hV⟩ := hc.exists_isGreatest hn
  change IsGreatest _ (sSup _)
  rw [hV.csSup_eq]
  exact hV

/-- The genuine attained selection value is nonnegative on every actual nonnegative source budget profile.
Use: The genuine attained selection value is nonnegative on every actual nonnegative source budget profile.
Article: main_krylov, thm:select, true attained finite-scenario transverse maxima.
Proof: The true zero scenario is feasible and has actual zero common-tilt variation. -/
theorem selectionValue_nonneg (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : Fin (N-1) → ℝ≥0) : 0≤selectionValue base g N ω := by
  apply (selectionValue_attained base g N ω).2
  refine ⟨0,(scenarioBudget_zero_mem (n := n) ω).1,?_⟩
  simp only [map_zero,norm_zero]
end
end krylov.Envelope

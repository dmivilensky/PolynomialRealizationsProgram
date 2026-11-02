import krylov.OneGradient.KnownBaseTwoQueryGuarantee
import krylov.Information.AdmissibleTwin
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), full original admissible scenario dictionary.
Use: identify the genuine two-query known-base guarantee with the existing
whole original Scenario.Admissible class at zero base-prior radius.
Source: exact positive-root reconstruction, the true two evaluated queries
and the existing independent increment/output physical scenario budgets.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.Secant krylov.Information
open scoped Matrix.Norms.L2Operator

/-- A true zero known-base prior budget fixes the whole physical base
matrix exactly, rather than only its observed Krylov restriction.
Use: the two-query minimax guarantee covers the existing original zero-prior
scenario class with its genuine initial physical matrix.
Article: main_krylov, thm:local(c), c=0 source class.
Proof: zero true relative norm makes the actual canonical displacement
zero. Positive-root reconstruction gives zero physical displacement. -/
theorem knownBase_zero_prior_eq
    (base B : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef)
    (hbudget : relativeBudget base (B-base)≤0) : B=base := by
  have hz : relativeOperator base (B-base)=0 := norm_eq_zero.mp (le_antisymm hbudget (norm_nonneg _))
  have he := relativeOperator_reconstruct base (B-base) hb
  rw [hz,Matrix.mul_zero,Matrix.zero_mul] at he
  exact sub_eq_zero.mp he.symm

/-- The genuine original physical two-query scenario associated with
arbitrary second and output matrices. Its only relevant increment is C-A;
its independent unevaluated output perturbation is B-C.
Use: every matrix quantified by the known-base guarantee is an actual
member of the preexisting original physical scenario structure.
Article: main_krylov, thm:local(c), true original scenario realization. -/
def knownBaseTwoQueryScenario (base C B : Matrix (Fin 2) (Fin 2) ℝ) : Scenario 2 where
  base := base
  increment := fun _ => C-base
  terminal := B-C
  correction := 0

/-- Every original symmetric budgeted matrix pair gives a genuine
admissible zero-prior source scenario, with all original budget fields.
Use: the all-method lower adversaries obey the existing source class.
Article: main_krylov, thm:local(c), genuine source admissibility.
Proof: the exact known base has zero displacement, the true increment and
output differences obey their given relative budgets, and correction
perturbations vanish identically. -/
theorem knownBaseTwoQueryScenario_admissible
    (base C B : Matrix (Fin 2) (Fin 2) ℝ) (hb : base.PosDef) (hC : C.IsSymm) (hB : B.IsSymm)
    (eta radius : ℝ) (hbudget : relativeBudget base (C-base)≤ eta)
    (houtput : relativeBudget base (B-C)≤ radius) :
    (knownBaseTwoQueryScenario base C B).Admissible 1 base 0 (fun _ => eta) radius 0 := by
  refine ⟨hb,?_,fun _ _ => ⟨hC.sub hb.isHermitian.isSymm,hbudget⟩,hB.sub hC,houtput,?_⟩
  · simp only [knownBaseTwoQueryScenario,sub_self,relativeBudget,relativeOperator,
      Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero,le_refl]
  · intro k _
    refine ⟨Matrix.isSymm_zero,?_⟩
    simp only [knownBaseTwoQueryScenario,Pi.zero_apply,relativeBudget,relativeOperator,
      Matrix.mul_zero,Matrix.zero_mul,chebyshev1.opNorm,norm_zero,le_refl]

/-- Every genuine scenario with the exact known base has the identical
complete two-query history to its original prescribed two physical probes.
Use: source-wide estimates concern the preexisting true scenario executor.
Article: main_krylov, thm:local(c), actual scenario execution dictionary.
Proof: the first physical probe is the actual known base and the second
is its true increment sum. Execute the literal two recorded updates. -/
theorem knownBaseTwoQueryScenario_histories
    (S : Scenario 2) (base : Matrix (Fin 2) (Fin 2) ℝ) (hbase : S.base=base)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2)) :
    oneGradientRun m S.probeOracle g 2=
      oneGradientRun m (twoQueryOperators (cgOperator base) (cgOperator (S.probe 1))) g 2 := by
  change oneGradientAdvance m (cgOperator (S.probe 1)) (oneGradientAdvance m (cgOperator (S.probe 0)) ⟨g,[]⟩)=_
  have hp0 : S.probe 0=base := by simp only [Scenario.probe,Finset.sum_range_zero,add_zero,hbase]
  rw [hp0]
  rfl

end
end krylov.OneGradient

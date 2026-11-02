import krylov.Correction.ScenarioExpansion
import krylov.Correction.GatedScenarioBudget

/-!
Article: main_krylov, thm:UCq, exact original terminal source matrices.
Use: Express every actual canonical probe and correction operator in the
same finite matrix coordinates as the measured terminal staircase calculation.
Source: the proved original canonical path and root-congruence identities;
genuine finite source zero extension and actual symmetric increment arrays.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The actual canonical probe matrix of the original finite source, including its true zero-extended increments.
Use: Identify the genuine source matrix path in the quantitative terminal response.
Article: main_krylov, thm:UCq.
-/
def scenarioCanonicalMatrix (Θ : CanonicalScenario n N) (j : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  1+∑ l ∈ range j, matrixSequenceExtension (N-1) Θ.1 l

/-- The genuine canonical source matrix has exactly its original consecutive source increment.
Use: Discharge the clean-model flag identity's true increment equation.
Article: main_krylov, thm:UCq.
Proof: Separate the last actual finite prefix summand and cancel the common matrix prefix.
-/
theorem scenarioCanonicalMatrix_increment (Θ : CanonicalScenario n N) (j : ℕ) :
    scenarioCanonicalMatrix Θ (j+1)-scenarioCanonicalMatrix Θ j=matrixSequenceExtension (N-1) Θ.1 j := by
  simp only [scenarioCanonicalMatrix,sum_range_succ]
  abel

/-- Every genuine canonical probe matrix from the original symmetric finite scenario space is symmetric.
Use: Derive the actual operator symmetry in the terminal search and clean-model identities.
Article: main_krylov, thm:UCq.
Proof: The identity and every actual zero-extended source increment are symmetric; transpose their true finite sum.
-/
theorem scenarioCanonicalMatrix_symm (Θ : symmetricScenarios n N) (j : ℕ) :
    (scenarioCanonicalMatrix Θ.val j).IsSymm := by
  change (1+∑ l ∈ range j, matrixSequenceExtension (N-1) Θ.val.1 l)ᵀ=_
  rw [Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_sum]
  congr 1
  apply sum_congr rfl
  intro l _hl
  exact (symmetricScenario_increment_symm Θ l).eq

/-- The original finite source has a genuine zero increment at its last correction index.
Use: Remove the artificial final zero summand in full-basis model coordinates.
Article: main_krylov, thm:UCq.
Proof: This index lies outside the original increment array, so its actual zero-extension branch applies.
-/
theorem scenario_last_increment_zero (Θ : CanonicalScenario n N) :
    matrixSequenceExtension (N-1) Θ.1 (N-1)=0 := by
  exact dite_eq_right (by omega)

/-- The actual source probe matrix is constant from its last correction index to the full-model terminal index.
Use: Match the real last correction operator with the exact clean-model full-basis factorization.
Article: main_krylov, thm:UCq.
Proof: The empty horizon is immediate; otherwise use the true consecutive increment identity and the original last zero increment.
-/
theorem scenarioCanonicalMatrix_terminal (Θ : CanonicalScenario n N) :
    scenarioCanonicalMatrix Θ N=scenarioCanonicalMatrix Θ (N-1) := by
  cases N with
  | zero => rfl
  | succ k =>
    have hi := scenarioCanonicalMatrix_increment Θ k
    have hz : matrixSequenceExtension (k+1-1) Θ.1 k=0 := by
      simpa only [Nat.add_sub_cancel] using scenario_last_increment_zero Θ
    rw [hz] at hi
    simpa only [Nat.add_sub_cancel] using sub_eq_zero.mp hi

/-- The actual physical source probe has exactly its genuine canonical finite source matrix.
Use: Preserve original queried operators in the quantitative terminal calculation.
Article: main_krylov, thm:UCq.
Proof: Reuse the proved canonical affine-path identity and the real matrix/operator sum dictionary.
-/
theorem scenarioProbe_canonicalMatrix (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (Θ : CanonicalScenario n N) (j : ℕ) :
    canonicalOperator base (scenarioProbe base Θ j)=cgOperator (scenarioCanonicalMatrix Θ j) := by
  rw [scenarioProbe,canonicalFCPath_canonicalOperator base hb]
  simp only [scenarioCanonicalMatrix,cgOperator,map_add,map_one]
  rfl

/-- The actual physical source correction operator has exactly its own genuine canonical probe matrix plus the original independent correction defect.
Use: Identify the true last model-query operator in source variables.
Article: main_krylov, thm:UCq.
Proof: Apply exact canonical additivity, genuine positive-root congruence cancellation and the true source-probe matrix identity.
-/
theorem scenarioCorrection_canonicalMatrix (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (Θ : CanonicalScenario n N) (j : ℕ) :
    canonicalOperator base (scenarioCorrection base Θ j)=
      cgOperator (scenarioCanonicalMatrix Θ j+matrixSequenceExtension N Θ.2 j) := by
  rw [scenarioCorrection,canonicalOperator_add,canonicalOperator_root_congruence base _ hb,
    scenarioProbe_canonicalMatrix base hb]
  simp only [cgOperator,map_add]

end
end krylov.Correction

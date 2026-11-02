import krylov.Envelope.ScenarioBudgets
import krylov.Envelope.ProjectionMatrices
import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioPaths
import krylov.Envelope.ForcedAbsorbedResponse

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Use: absorb actual finite canonical scenarios without changing their
real correction defects or perturbation budgets, and prove the genuine
forced minus-tilt response of every actual smooth source-class member.
Source: actual canonical complementary-flag compression, true finite
scenario paths and the constructed genuine quadratic information fibre.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- Actual finite matrix scenario extension reads every genuine valid coordinate exactly.
Use: Actual finite matrix scenario extension reads every genuine valid coordinate exactly.
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Proof: The real finite index satisfies its actual extension bound. -/
theorem matrixSequenceExtension_fin {p : ℕ} (data : Fin p → Matrix (Fin n) (Fin n) ℝ) (i : Fin p) :
    matrixSequenceExtension p data i.val=data i := dite_eq_left i.isLt

/-- The genuine finite canonical absorbed scenario preserving every actual correction defect.
Use: The genuine finite canonical absorbed scenario preserving every actual correction defect.
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Proof: Compress each true canonical increment by its actual complementary explored flag and retain the real correction array. -/
def absorbedScenario (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (Θ : CanonicalScenario n N) : CanonicalScenario n N :=
  ((fun i => absorbedIncrements base g (matrixSequenceExtension (N-1) Θ.1) i.val),Θ.2)

/-- Extending a genuine finite absorbed scenario gives exactly the actual absorbed canonical increment sequence.
Use: Extending a genuine finite absorbed scenario gives exactly the actual absorbed canonical increment sequence.
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Proof: True valid coordinates agree by construction; actual absent coordinates are real zero increments and their genuine compressions remain zero. -/
theorem absorbedScenario_extension (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (Θ : CanonicalScenario n N) :
    matrixSequenceExtension (N-1) (absorbedScenario base g Θ).1=
      absorbedIncrements base g (matrixSequenceExtension (N-1) Θ.1) := by
  -- Genuine valid coordinates agree exactly, while true zero defaults have actual zero absorbed compression.
  funext k
  change matrixSequenceExtension (N-1) (fun i => absorbedIncrements base g (matrixSequenceExtension (N-1) Θ.1) i.val) k=_
  by_cases hk : k<N-1
  · simp only [matrixSequenceExtension,dite_eq_left hk]
  · rw [show matrixSequenceExtension (N-1) (fun i => absorbedIncrements base g (matrixSequenceExtension (N-1) Θ.1) i.val) k=0 from dite_eq_right hk]
    rw [absorbedIncrements_matrix]
    have hz : matrixSequenceExtension (N-1) Θ.1 k=0 := dite_eq_right hk
    rw [hz,Matrix.mul_zero,Matrix.zero_mul]

/-- Actual canonical absorption preserves every genuine finite source scenario budget profile.
Use: Actual canonical absorption preserves every genuine finite source scenario budget profile.
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Proof: Real symmetric compression preserves actual increment symmetry and contracts each true spectral norm budget; genuine correction defects remain the actual original array. -/
theorem absorbedScenario_budget (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (ω : Fin (N-1) → ℝ≥0) (Θ : CanonicalScenario n N) (hΘ : Θ∈scenarioBudget N ω) :
    absorbedScenario base g Θ∈scenarioBudget N ω := by
  -- Actual compression contracts each true individual increment budget and preserves the real correction-defect array.
  rcases hΘ with ⟨hE,hF⟩
  refine ⟨?_,hF⟩
  intro i
  refine ⟨absorbedIncrements_symm base g (matrixSequenceExtension (N-1) Θ.1) i.val (by
    rw [matrixSequenceExtension_fin]
    exact (hE i).1),?_⟩
  apply (absorbedIncrements_norm_le base g (matrixSequenceExtension (N-1) Θ.1) i.val).trans
  rw [matrixSequenceExtension_fin]
  exact (hE i).2

/-- Every actual genuine smooth globally CG-consistent source-class member has forced finite-scenario variation equal to minus the original true common tilt on the real absorbed scenario.
Use: Every actual genuine smooth globally CG-consistent source-class member has forced finite-scenario variation equal to minus the original true common tilt on the real absorbed scenario.
Article: main_krylov, thm:select, genuine finite absorbed scenarios and forced actual variations.
Proof: Identify the true actual scenario-axis derivative, its genuine absorbed line path and real analytic correction path. Apply the proved genuine class-quantified absorbed quadratic information-fibre response with actual primitive membership already derived. -/
theorem forced_absorbed_scenarioVariation (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N)
    (hE : ∀ i, (Θ.1 i).IsSymm) :
    scenarioVariation M.policy base g N (absorbedScenario base g Θ)=
      -commonTilt base g (canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1)) N := by
  -- Identify the genuine absorbed source path before applying the real class-quantified quadratic information fibre.
  let Ξ := absorbedScenario base g Θ
  let B := fun t : ℝ => scenarioCorrection base (t • Ξ)
  have hB0 : B 0=fun _ => cgOperator base := by
    dsimp only [B]
    rw [zero_smul,scenarioCorrection_zero]
  have hB (k : ℕ) : DifferentiableAt ℝ (fun t => B t k) 0 :=
    (scenarioCorrection_path_analytic base Ξ k).differentiableAt
  have hv := scenarioVariation_actual M base hb g N hcount Ξ
  have he : (fun t : ℝ => scenarioGradient M.policy base g N (t • Ξ))=
      fun t => probedGradient M.policy (canonicalFCPath base (absorbedIncrements base g (matrixSequenceExtension (N-1) Θ.1)) t) (B t) g N := by
    funext t
    unfold scenarioGradient
    rw [scenarioProbe_scale,absorbedScenario_extension]
  rw [he] at hv
  rw [hv]
  exact forced_absorbed_response M base hb g N hN hcount (matrixSequenceExtension (N-1) Θ.1)
    (fun l hl => by rw [show matrixSequenceExtension (N-1) Θ.1 l=Θ.1 ⟨l,hl⟩ from dite_eq_left hl];exact hE ⟨l,hl⟩)
    B hB0 (fun k _ => hB k)
end
end krylov.Envelope

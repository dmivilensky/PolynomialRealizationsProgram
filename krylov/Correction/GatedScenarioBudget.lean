import krylov.Correction.GatedSpectralCycle
import krylov.Envelope.ScenarioCoordinates
import krylov.Stability.CanonicalFCOperators

/-!
Article: main_krylov, thm:UCg, the original finite source budget.
Use: Derive both true canonical operator allowances from the actual finite
increment and correction-defect arrays, including every zero budget.
Source: exact positive-root congruence cancellation and finite spectral
norm subadditivity on the genuine canonical source path.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine canonical operator coordinates preserve the sum of two physical operators.
Use: Instantiate the actual uniform gated theorem on original finite source variables.
Article: main_krylov, thm:UCg(i,ii).
Proof: Evaluate the two actual compositions and apply linearity.
-/
theorem canonicalOperator_add (base : Matrix (Fin n) (Fin n) ℝ)
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    canonicalOperator base (A+B)=canonicalOperator base A+canonicalOperator base B := by
  ext v
  simp only [canonicalOperator,ContinuousLinearMap.comp_apply,_root_.add_apply,map_add]

/-- An actual physical root-congruence perturbation has exactly its original canonical matrix operator.
Use: Instantiate the actual uniform gated theorem on original finite source variables.
Article: main_krylov, thm:UCg(i,ii).
Proof: The positive metric root has a genuine inverse; cancel its two factors in the actual relative congruence.
-/
theorem canonicalOperator_root_congruence (base F : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    canonicalOperator base (cgOperator (metricRoot base*F*metricRoot base))=cgOperator F := by
  rw [cgOperator,canonicalOperator_matrix]
  congr 1
  unfold relativeOperator
  calc
    _ = ((metricRoot base)⁻¹*metricRoot base)*F*(metricRoot base*(metricRoot base)⁻¹) := by noncomm_ring
    _ = F := by rw [Matrix.nonsing_inv_mul _ (metricRoot_det_unit base hb),
      Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),Matrix.one_mul,Matrix.mul_one]

/-- The true zero extension of a finite bounded source array has the same bound at every index.
Use: Instantiate the actual uniform gated theorem on original finite source variables.
Article: main_krylov, thm:UCg(i,ii).
Proof: The finite branch uses its original coordinate budget and the default branch uses nonnegativity.
-/
theorem matrixSequenceExtension_norm_le (p k : ℕ) (data : Fin p → Matrix (Fin n) (Fin n) ℝ)
    {ω : ℝ} (hω : 0≤ω) (hdata : ∀ i, ‖data i‖≤ω) :
    ‖matrixSequenceExtension p data k‖≤ω := by
  by_cases hk : k<p
  · simpa only [matrixSequenceExtension,dite_eq_left hk] using hdata ⟨k,hk⟩
  · simpa only [matrixSequenceExtension,dite_eq_right hk,norm_zero] using hω

/-- Every original finite increment/defect scenario supplies the true dimension-times-maximum operator allowances.
Use: Instantiate the actual uniform gated theorem on original finite source variables.
Article: main_krylov, thm:UCg(i,ii).
Proof: Bound the genuine canonical cumulative path by its finite increment sum, then add the exact canonical correction defect. No scenario budget or output estimate is assumed beyond the individual source entry bounds.
-/
theorem scenario_canonical_operator_budgets (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (Θ : CanonicalScenario n N) {ω : ℝ} (hω : 0≤ω)
    (hE : ∀ i, ‖Θ.1 i‖≤ω) (hF : ∀ i, ‖Θ.2 i‖≤ω) (k : ℕ) (hk : k<N) :
    ‖canonicalOperator base (scenarioProbe base Θ k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤((N : ℝ)+1)*ω ∧
    ‖canonicalOperator base (scenarioCorrection base Θ k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤((N : ℝ)+1)*ω := by
  have hA : ‖canonicalOperator base (scenarioProbe base Θ k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤(N : ℝ)*ω := by
    apply (canonicalFCPath_budget_bound base hb (matrixSequenceExtension (N-1) Θ.1) N k hk.le).trans
    calc
      _ ≤ ∑ _i ∈ range N, ω := sum_le_sum (fun i _ => matrixSequenceExtension_norm_le (N-1) i Θ.1 hω hE)
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]
  refine ⟨hA.trans (by nlinarith),?_⟩
  rw [scenarioCorrection,canonicalOperator_add,canonicalOperator_root_congruence base _ hb]
  calc
    _ = ‖(canonicalOperator base (scenarioProbe base Θ k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))+
        cgOperator (matrixSequenceExtension N Θ.2 k)‖ := by congr 1; abel
    _ ≤ ‖canonicalOperator base (scenarioProbe base Θ k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖+
        ‖cgOperator (matrixSequenceExtension N Θ.2 k)‖ := norm_add_le _ _
    _ ≤ (N : ℝ)*ω+ω := add_le_add hA (by
      simpa only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] using matrixSequenceExtension_norm_le N k Θ.2 hω hF)
    _ = _ := by ring

end
end krylov.Correction

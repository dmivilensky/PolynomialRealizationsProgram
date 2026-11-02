import krylov.Stability.CanonicalRegularity
import krylov.Methods.FiniteOracleCharts
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Use: represent true canonical increment and correction-defect scenarios
in their genuine finite-dimensional space and derive real source-path
scaling, reference values and primitive operator regularity.
Source: actual canonical affine probe segments, true positive-root
correction defects and standard finite coordinate smoothness.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
open scoped BigOperators Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine finite canonical source increment and correction-defect arrays.
Use: Keep all actual horizon operators in one true finite-dimensional scenario space.
Article: main_krylov, thm:select, actual finite canonical scenarios.
Proof: The genuine source has one canonical increment per old-step boundary and one real correction defect per iteration. -/
abbrev CanonicalScenario (n N : ℕ) :=
  (Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) × (Fin N → Matrix (Fin n) (Fin n) ℝ)

/-- A genuine finite matrix scenario array extended by true zero beyond its actual horizon.
Use: A genuine finite matrix scenario array extended by true zero beyond its actual horizon.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Read the genuine finite coordinate before its actual bound and use a real zero default afterwards. -/
def matrixSequenceExtension (p : ℕ) (data : Fin p → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if hk : k<p then data ⟨k,hk⟩ else 0

/-- The actual zero finite matrix scenario extends to the genuine zero matrix sequence.
Use: The actual zero finite matrix scenario extends to the genuine zero matrix sequence.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Both true finite/default branches return actual zero. -/
theorem matrixSequenceExtension_zero (p k : ℕ) :
    matrixSequenceExtension p (0 : Fin p → Matrix (Fin n) (Fin n) ℝ) k=0 := by
  by_cases hk : k<p <;> simp only [matrixSequenceExtension,hk,dite_true,dite_false,Pi.zero_apply]

/-- Actual finite matrix scenario extension preserves genuine real perturbation scaling.
Use: Actual finite matrix scenario extension preserves genuine real perturbation scaling.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Read the true scaled coordinate or use actual zero scalar multiplication in the default branch. -/
theorem matrixSequenceExtension_smul (p k : ℕ) (data : Fin p → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    matrixSequenceExtension p (t • data) k=t • matrixSequenceExtension p data k := by
  by_cases hk : k<p <;> simp only [matrixSequenceExtension,hk,dite_true,dite_false,Pi.smul_apply,smul_zero]

/-- The actual source line-operator sequence of a genuine finite canonical scenario.
Use: The actual source line-operator sequence of a genuine finite canonical scenario.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Use the true canonical affine source path with the actual finite increment array. -/
def scenarioProbe (base : Matrix (Fin n) (Fin n) ℝ)
    (Θ : CanonicalScenario n N) :
    ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) 1

/-- The actual source correction-operator sequence of a genuine finite canonical scenario.
Use: The actual source correction-operator sequence of a genuine finite canonical scenario.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Add its real positive-root correction defect to the actual current probe segment. -/
def scenarioCorrection (base : Matrix (Fin n) (Fin n) ℝ)
    (Θ : CanonicalScenario n N) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  scenarioProbe base Θ k+cgOperator (metricRoot base*matrixSequenceExtension N Θ.2 k*metricRoot base)

/-- The genuine zero scenario has exactly the actual constant quadratic line operators.
Use: The genuine zero scenario has exactly the actual constant quadratic line operators.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: The true finite increments are zero, so their actual canonical cumulative drift vanishes. -/
theorem scenarioProbe_zero (base : Matrix (Fin n) (Fin n) ℝ) :
    scenarioProbe (N := N) base 0=fun _ => cgOperator base := by
  funext k
  simp only [scenarioProbe,Prod.fst_zero,matrixSequenceExtension_zero,canonicalFCPath,cumulativeDrift,
    Finset.sum_const_zero,Matrix.mul_zero,Matrix.zero_mul,map_zero,one_smul,add_zero]

/-- The genuine zero scenario has exactly the actual constant quadratic correction operators.
Use: The genuine zero scenario has exactly the actual constant quadratic correction operators.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Both the true canonical line drift and actual independent correction defect vanish. -/
theorem scenarioCorrection_zero (base : Matrix (Fin n) (Fin n) ℝ) :
    scenarioCorrection (N := N) base 0=fun _ => cgOperator base := by
  funext k
  simp only [scenarioCorrection,scenarioProbe_zero,Prod.snd_zero,matrixSequenceExtension_zero,
    Matrix.mul_zero,Matrix.zero_mul,cgOperator,map_zero,add_zero]

/-- Scaling a genuine finite scenario traces exactly the actual canonical line perturbation path.
Use: Scaling a genuine finite scenario traces exactly the actual canonical line perturbation path.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Actual finite extension, true prefix summation and genuine metric-root congruence all preserve real perturbation scaling. -/
theorem scenarioProbe_scale (base : Matrix (Fin n) (Fin n) ℝ)
    (Θ : CanonicalScenario n N) (t : ℝ) :
    scenarioProbe base (t • Θ)=canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) t := by
  funext k
  change canonicalFCPath base (matrixSequenceExtension (N-1) (t • Θ.1)) 1 k=_
  simp only [matrixSequenceExtension_smul,canonicalFCPath,cumulativeDrift,
    ← Finset.smul_sum,Matrix.mul_smul,Matrix.smul_mul,map_smul,one_smul]

/-- Scaling a genuine finite scenario traces exactly the actual canonical correction path with its true independent correction defect.
Use: Scaling a genuine finite scenario traces exactly the actual canonical correction path with its true independent correction defect.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Use genuine line-path scaling and the true linear metric-root correction-defect congruence. -/
theorem scenarioCorrection_scale (base : Matrix (Fin n) (Fin n) ℝ)
    (Θ : CanonicalScenario n N) (t : ℝ) (k : ℕ) :
    scenarioCorrection base (t • Θ) k=canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) t k+
      t • cgOperator (metricRoot base*matrixSequenceExtension N Θ.2 k*metricRoot base) := by
  change scenarioProbe base (t • Θ) k+cgOperator (metricRoot base*matrixSequenceExtension N (t • Θ.2) k*metricRoot base)=_
  simp only [scenarioProbe_scale,matrixSequenceExtension_smul,Matrix.mul_smul,Matrix.smul_mul,cgOperator,map_smul]

/-- The actual line and correction operator coordinates are genuinely C-r functions of the true finite canonical scenario.
Use: The actual line and correction operator coordinates are genuinely C-r functions of the true finite canonical scenario.
Article: main_krylov, thm:select, actual finite canonical scenario coordinates.
Proof: Actual finite coordinate projections and genuine zero defaults are smooth. Apply the proved real canonical segment calculus and actual positive-root correction-defect matrix/operator smoothness. -/
theorem scenarioPrimitive_regular (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (k : ℕ) (r : WithTop ℕ∞) :
    ContDiffAt ℝ r (fun Θ : CanonicalScenario n N => scenarioProbe base Θ k) 0 ∧
    ContDiffAt ℝ r (fun Θ : CanonicalScenario n N => scenarioCorrection base Θ k) 0 := by
  -- Every genuine finite increment and real correction defect is an actual smooth coordinate projection or true zero default.
  have hE (l : ℕ) : ContDiffAt ℝ r (fun Θ : CanonicalScenario n N =>
      matrixSequenceExtension (N-1) Θ.1 l) 0 := by
    by_cases hl : l<N-1
    · simp only [matrixSequenceExtension,dite_eq_left hl]
      exact contDiffAt_pi.mp contDiffAt_fst (⟨l,hl⟩ : Fin (N-1))
    · simp only [matrixSequenceExtension,dite_eq_right hl]
      exact contDiffAt_const
  have hF : ContDiffAt ℝ r (fun Θ : CanonicalScenario n N =>
      matrixSequenceExtension N Θ.2 k) 0 := by
    by_cases hk : k<N
    · simp only [matrixSequenceExtension,dite_eq_left hk]
      exact contDiffAt_pi.mp contDiffAt_snd (⟨k,hk⟩ : Fin N)
    · simp only [matrixSequenceExtension,dite_eq_right hk]
      exact contDiffAt_const
  have hA := canonicalFCPath_contDiffAt (fun _ : CanonicalScenario n N => base) (fun Θ => matrixSequenceExtension (N-1) Θ.1) 0
    contDiffAt_const (Eventually.of_forall (fun _ => hb)) hE k
  refine ⟨hA,?_⟩
  exact hA.add (matrixOperator_contDiffAt _ 0 ((contDiffAt_const.mul hF).mul contDiffAt_const))
end
end krylov.Envelope

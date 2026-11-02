import krylov.Envelope.ScenarioVariation
import krylov.Envelope.ScenarioRFC
import krylov.Envelope.CanonicalDirectionalFiltration
import krylov.Envelope.ResponseAbsorption
import krylov.Envelope.ScenarioAbsorption

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Use: express the actual canonical full and unexplored first variations
as true continuous linear maps on finite source scenarios, and prove
genuine common-response invariance under budget-preserving absorption.
Source: actual primitive smooth-cycle regularity and the proved full
raw-method canonical filtration and absorbed-response geometry.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual canonical first derivative of the genuine finite-scenario raw cycle.
Use: The actual canonical first derivative of the genuine finite-scenario raw cycle.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Compose the real actual cycle Frechet derivative with its true inverse reference metric root. -/
def scenarioCanonicalDerivative (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    CanonicalScenario n N →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  cgOperator (metricRoot base)⁻¹ ∘L fderiv ℝ (scenarioGradient m base g N) 0

/-- The genuine continuous linear common unexplored variation map on the actual finite source scenario space.
Use: The genuine continuous linear common unexplored variation map on the actual finite source scenario space.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Use the real complementary projection of the actual RFC canonical cycle derivative. -/
def scenarioUnexplored (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) :
    CanonicalScenario n N →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.id ℝ _-(exploredFlag base g N).starProjection) ∘L
    scenarioCanonicalDerivative (rfcMethod fullMemory 1) base g N

/-- The actual canonical derivative of every genuine smooth source-class member minus its real explored variation equals the true common frozen unexplored source response.
Use: The actual canonical derivative of every genuine smooth source-class member minus its real explored variation equals the true common frozen unexplored source response.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Derive actual finite scenario coefficient regularity and true active reference domains, apply the genuine ambient raw-method filtration, and identify the real scenario axis and canonical derivative by the true chain rule. -/
theorem scenarioCanonicalDerivative_common (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioCanonicalDerivative M.policy base g N Θ-scenarioVariation M.policy base g N Θ=
      commonTransverseResponse base g (canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1)) N := by
  -- Use the actual finite source scenario maps to derive genuine primitive operator domains and real reference activity.
  let A := scenarioProbe base (N := N)
  let B := scenarioCorrection base (N := N)
  have hregular (k : ℕ) := scenarioPrimitive_regular base hb (N := N) k (r := 2)
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have hf := actual_fderiv_common_transverse M.memory M.policy M.consistent M.admissible
    (fun _ : CanonicalScenario n N => base) (fun _ => g) A B 0 Θ N contDiffAt_const
    (Filter.Eventually.of_forall (fun _ => hb)) (fun k _ => (hregular k).1) (fun k _ => (hregular k).2)
    contDiffAt_const (scenarioProbe_zero base) (scenarioCorrection_zero base)
    hpre (M.smooth _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N hpre)
    (fun _ => rfl) (fun _ => rfl)
  -- The true inverse root is fixed on this actual scenario space; the genuine chain rule identifies the canonical Frechet derivative.
  have hF : fderiv ℝ (fun p => cgOperator (metricRoot base)⁻¹ (scenarioGradient M.policy base g N p)) 0=
      cgOperator (metricRoot base)⁻¹ ∘L fderiv ℝ (scenarioGradient M.policy base g N) 0 :=
    ((cgOperator (metricRoot base)⁻¹).hasFDerivAt.comp 0
      ((scenarioGradient_regular M base hb g N hcount).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  change fderiv ℝ (fun p => cgOperator (metricRoot base)⁻¹ (scenarioGradient M.policy base g N p)) 0 Θ-
    (exploredFlag base g N).starProjection
      (fderiv ℝ (fun p => cgOperator (metricRoot base)⁻¹ (scenarioGradient M.policy base g N p)) 0 Θ)=_ at hf
  rw [hF] at hf
  change scenarioCanonicalDerivative M.policy base g N Θ-scenarioVariation M.policy base g N Θ=_ at hf
  have he : (fun t : ℝ => A (0+t • Θ))=canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1) := by
    funext t
    rw [zero_add]
    exact scenarioProbe_scale base Θ t
  rw [he] at hf
  exact hf

/-- The genuine continuous linear unexplored scenario map equals the actual common frozen source response.
Use: The genuine continuous linear unexplored scenario map equals the actual common frozen source response.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Specialize the real raw-method filtration to the genuine primitive smooth RFC class. -/
theorem scenarioUnexplored_actual (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioUnexplored base g N Θ=
      commonTransverseResponse base g (canonicalFCPath base (matrixSequenceExtension (N-1) Θ.1)) N :=
  scenarioCanonicalDerivative_common (smoothRFCClass fullMemory (fun _ hk => hk) 1) base hb g N hcount Θ

/-- Every actual smooth source-class canonical derivative is exactly the true common unexplored variation plus its genuine explored method variation.
Use: Every actual smooth source-class canonical derivative is exactly the true common unexplored variation plus its genuine explored method variation.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Rearrange the actual common-response filtration identity on the genuine finite source scenario space. -/
theorem scenarioCanonicalDerivative_split (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioCanonicalDerivative M.policy base g N Θ=
      scenarioUnexplored base g N Θ+scenarioVariation M.policy base g N Θ := by
  have he := scenarioCanonicalDerivative_common M base hb g N hcount Θ
  rw [← scenarioUnexplored_actual base hb g N hcount Θ] at he
  exact sub_eq_iff_eq_add.mp he

/-- The actual common unexplored first variation is unchanged by genuine finite absorbed scenario compression.
Use: The actual common unexplored first variation is unchanged by genuine finite absorbed scenario compression.
Article: main_krylov, thm:E and s3:cor:qn, genuine linear common unexplored scenario response.
Proof: Identify both real responses with their true source expressions and apply actual absorbed-response invariance. -/
theorem scenarioUnexplored_absorbed (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g) (Θ : CanonicalScenario n N) :
    scenarioUnexplored base g N (absorbedScenario base g Θ)=scenarioUnexplored base g N Θ := by
  rw [scenarioUnexplored_actual base hb g N hcount,scenarioUnexplored_actual base hb g N hcount,
    absorbedScenario_extension,commonTransverseResponse_absorbedIncrements base hb g (matrixSequenceExtension (N-1) Θ.1) N hcount]
end
end krylov.Envelope

import krylov.Envelope.JointScenarioRegularity
import krylov.Envelope.FDerivScenarioSlice
import krylov.Envelope.ScenarioFrozenLinearity

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, actual varying-reference finite scenario output.
Use: derive genuine joint output regularity and identify real reference-
preserving derivatives with the true canonical source scenario derivative.
Source: actual primitive smooth source-class execution, positive inverse-root
calculus and the genuine Frechet scenario-slice chain rule.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n N : ℕ}

/-- The genuine canonical output of the actual method jointly parameterized by its true reference and finite source scenario.
Use: The genuine canonical output of the actual method jointly parameterized by its true reference and finite source scenario.
Article: main_krylov, thm:E and s3:cor:qn, actual varying-reference finite scenario output.
Proof: Execute the real finite source operators and apply their actual fixed-reference inverse metric root. -/
def jointScenarioOutput (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (p : X × CanonicalScenario n N) : EuclideanSpace ℝ (Fin n) :=
  cgOperator (metricRoot (base p.1))⁻¹ (scenarioGradient m (base p.1) (g p.1) N p.2)

/-- The actual canonical source-cycle output is jointly C-two at every genuine active positive reference and zero source scenario.
Use: The actual canonical source-cycle output is jointly C-two at every genuine active positive reference and zero source scenario.
Article: main_krylov, thm:E and s3:cor:qn, actual varying-reference finite scenario output.
Proof: Derive true joint line and correction primitive regularity, actual source-class cycle domains and genuine variable inverse-root regularity. -/
theorem jointScenarioOutput_regular (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n)) (x : X)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : ContDiffAt ℝ 2 g x)
    (hcount : N≤referenceAtomCount (base x) hpos.self_of_nhds (g x)) :
    ContDiffAt ℝ 2 (jointScenarioOutput M.policy base g N) (x,0) := by
  -- The actual joint chart retains the real base and initial gradient while exposing every genuine finite scenario coordinate.
  let b : X × CanonicalScenario n N → Matrix (Fin n) (Fin n) ℝ := fun p => base p.1
  let h : X × CanonicalScenario n N → EuclideanSpace ℝ (Fin n) := fun p => g p.1
  have hb' : ContDiffAt ℝ 2 b (x,0) := hb.comp _ contDiffAt_fst
  have hg' : ContDiffAt ℝ 2 h (x,0) := hg.comp _ contDiffAt_fst
  have hp' : ∀ᶠ p in 𝓝 ((x,0) : X × CanonicalScenario n N), (b p).PosDef := by
    change ∀ᶠ p : X × CanonicalScenario n N in 𝓝 (x,0), (base p.1).PosDef
    exact (continuous_fst.tendsto (x,(0 : CanonicalScenario n N))).eventually hpos
  have hAB (k : ℕ) := jointScenarioPrimitive_regular b (fun p : X × CanonicalScenario n N => p.2)
    (x,0) 2 hb' hp' contDiffAt_snd k
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator (base x)) (g x) i≠0 :=
    cg_nonstagnation _ hpos.self_of_nhds _ i (hi.trans_le hcount)
  have hG := smoothProbed_gradient_regular M.policy M.consistent
    (fun p => scenarioProbe (b p) p.2) (fun p => scenarioCorrection (b p) p.2) h (x,0) N
    (fun k _ => (hAB k).1) (fun k _ => (hAB k).2) hg' (cgOperator (base x))
    (scenarioProbe_zero _) (scenarioCorrection_zero _) (cgOperator_positive _ hpos.self_of_nhds).1
    (cgOperator_positive _ hpos.self_of_nhds).2 hpre
    (M.smooth _ (cgOperator_positive _ hpos.self_of_nhds).1 (cgOperator_positive _ hpos.self_of_nhds).2 _ N hpre)
  exact (matrixOperator_contDiffAt _ (x,0) (metricRoot_inverse_contDiffAt b (x,0) hb' hp')).clm_apply hG

/-- The genuine joint canonical output derivative along a real reference-preserving source scenario equals its actual fixed-reference canonical derivative.
Use: The genuine joint canonical output derivative along a real reference-preserving source scenario equals its actual fixed-reference canonical derivative.
Article: main_krylov, thm:E and s3:cor:qn, actual varying-reference finite scenario output.
Proof: Use the true affine scenario-slice derivative and the genuine inverse-root/cycle chain rule. -/
theorem jointScenarioOutput_scenario_derivative (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n)) (x : X)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ y in 𝓝 x, (base y).PosDef)
    (hg : ContDiffAt ℝ 2 g x)
    (hcount : N≤referenceAtomCount (base x) hpos.self_of_nhds (g x)) (Θ : CanonicalScenario n N) :
    fderiv ℝ (jointScenarioOutput M.policy base g N) (x,0) (0,Θ)=
      scenarioCanonicalDerivative M.policy (base x) (g x) N Θ := by
  rw [fderiv_scenario_slice _ x ((jointScenarioOutput_regular M base g x hb hpos hg hcount).differentiableAt (by norm_num))]
  have hc := ((cgOperator (metricRoot (base x))⁻¹).hasFDerivAt.comp 0
    ((scenarioGradient_regular M (base x) hpos.self_of_nhds (g x) N hcount).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  exact congrArg (fun L => L Θ) hc
end
end krylov.Envelope

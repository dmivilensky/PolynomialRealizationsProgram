import krylov.XR.CorrectedDictionary
import krylov.XR.LocalSelectedQuotient

/-!
Article: main_krylov, cor:xrF, literal Euclidean-split XR-F option.
Use: bind the original observed endpoint values to the Euclidean split
and the actual oversized and Hermitian gates. The native executor keeps
all original rank, deletion, Ritz, Radau, safeguard and rejection operations.
Source: the displayed XR algorithm and its Euclidean split alternative.
-/
namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant krylov.Functions
open scoped InnerProductSpace BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual Euclidean split at the current observed point. -/
def euclideanStoredSplit (x : E) (W : List (PairObservation E)) (i : Fin W.length) : ℝ :=
  inner ℝ (storedSteps W i) (x-(W.get i).anchor)/‖storedSteps W i‖^2-1/2

/-- Exact actual diagonal with the same oversized-term gate as XR-F. -/
def euclideanStoredValueTerm (x : E) (W : List (PairObservation E)) (i : Fin W.length) : ℝ :=
  let term:=12*euclideanStoredSplit x W i*(W.get i).valueDefect
  if |term| > storedPairing W i i/2 then 0 else term

/-- The Euclidean split changes only the true value diagonal. -/
def euclideanStoredValueModel (x : E) (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  storedModel W-diagonal (euclideanStoredValueTerm x W)

/-- The original complex gate, with the Euclidean corrected diagonal. -/
def euclideanCorrectedWindowPasses (theta : ℝ) (x : E) (W : List (PairObservation E)) : Prop :=
  ((euclideanStoredValueModel x W).map Complex.ofReal+
    (Complex.I/(theta:ℂ)) • (defect (storedPairing W)).map Complex.ofReal).PosDef

/-- Real value-model selection for the Euclidean option. -/
def selectedEuclideanModel (P : Parameters) (x : E) (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ := by
  classical
  exact if P.valuesEnabled=true ∧euclideanCorrectedWindowPasses P.windowThreshold x W
    then euclideanStoredValueModel x W else storedModel W

def euclideanAlgorithmModel {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    ModelResult (EuclideanSpace ℝ (Fin n)) := by
  classical
  let W₀ := rankWindow n S
  let o := modelDeletion P W₀
  let W := W₀.drop o
  let bounds := if W.length = 0 then S.bounds else updateBounds P.inflation S.bounds W
  let rho := fallbackCurvature bounds S.initialStep
  let u := if W.length = 0 then
      -(match bounds with | none => S.initialStep | some b => 2 / (b.1 + b.2)) • S.gradient
    else
      let s := storedSteps W
      let y := storedImages W
      let T := selectedEuclideanModel P S.point W
      let w := modelCoefficients s T S.gradient
      let virtual := S.gradient + combine y w
      let d := conjugacyDirection s y virtual
      if W.length = n ∨ d = 0 then combine s w
      else
        let b := bounds.getD (rho, rho)
        let curvature := observedTrialCurvature P W (storedModel W) d b
        combine s w + (-inner ℝ S.gradient d / curvature) • d
  exact ⟨W, bounds, u, rho, W₀.length, o⟩


/-- The actual Euclidean option uses the unchanged scalar executor and
true observations; no output or successful branch is an input. -/
def euclideanAlgorithmRun {n : ℕ} (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds:=none) : ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  run P n (euclideanAlgorithmModel P) f G (algorithmInitialState P f G x₀ bounds)

/-- Pair selection is identical for both literal split options. -/
theorem euclideanAlgorithmModel_pairs {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).pairs=(algorithmModel P S).pairs:=rfl

/-- The running Ritz bounds use the unchanged ordinary latest model. -/
theorem euclideanAlgorithmModel_bounds {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).bounds=(algorithmModel P S).bounds:=rfl

theorem euclideanAlgorithmModel_fallback {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).fallbackCurvature=(algorithmModel P S).fallbackCurvature:=rfl

theorem euclideanAlgorithmModel_pairsBeforeTest {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).pairsBeforeTest=(algorithmModel P S).pairsBeforeTest:=rfl

theorem euclideanAlgorithmModel_deleted {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).deletedByTest=(algorithmModel P S).deletedByTest:=rfl

/-- Literal Euclidean trial curvature still uses the ordinary Radau matrix. -/
def euclideanComputedCurvature {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) : ℝ :=
  let M:=euclideanAlgorithmModel P S
  observedTrialCurvature P M.pairs (storedModel M.pairs)
    (modelDirection (storedSteps M.pairs) (storedImages M.pairs) (selectedEuclideanModel P S.point M.pairs) S.gradient)
    (M.bounds.getD (M.fallbackCurvature,M.fallbackCurvature))

def euclideanTrialParameter {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) : ℝ := by
  classical
  let M := euclideanAlgorithmModel P S
  let W := M.pairs
  let s := storedSteps W
  let y := storedImages W
  let T := selectedEuclideanModel P S.point W
  let d := modelDirection s y T S.gradient
  exact if W.length = 0 then
      match M.bounds with | none => S.initialStep | some b => 2 / (b.1 + b.2)
    else if W.length = n ∨ d = 0 then 0
    else modelTrialLength s y T S.gradient
      (observedTrialCurvature P W (storedModel W) d
        (M.bounds.getD (M.fallbackCurvature, M.fallbackCurvature)))

/-- Any nonempty actually retained model is exactly its computed block
trial, including the full and zero-direction window-only cases. -/
theorem euclideanAlgorithmModel_direction_decomposition {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    let M := euclideanAlgorithmModel P S
    M.pairs.length ≠ 0 → M.direction =
      modelVirtualCorrection (storedSteps M.pairs) (selectedEuclideanModel P S.point M.pairs) S.gradient +
        euclideanTrialParameter P S • modelDirection (storedSteps M.pairs)
          (storedImages M.pairs) (selectedEuclideanModel P S.point M.pairs) S.gradient := by
  classical
  dsimp only
  intro hp
  unfold euclideanTrialParameter euclideanAlgorithmModel at *
  dsimp only at *
  rw [ite_eq_right hp]
  simp only [modelDirection, modelVirtualGradient, modelVirtualCorrection, modelTrialLength]
  split <;> simp_all only [zero_smul, add_zero]

/-- The genuine empty-window branch has precisely its computed scalar
times the negative cached gradient. -/
theorem euclideanAlgorithmModel_empty_direction {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hp : (euclideanAlgorithmModel P S).pairs.length = 0) :
    (euclideanAlgorithmModel P S).direction = euclideanTrialParameter P S • (-S.gradient) := by
  classical
  unfold euclideanTrialParameter euclideanAlgorithmModel at *
  dsimp only at *
  simp only [hp, ite_true, smul_neg, neg_smul]


end
end krylov.XR

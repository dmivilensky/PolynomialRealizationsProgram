import krylov.XR.Backtracking

/-!
Article: main_krylov, alg:xr, actual rejected-probe and accepted-step executor.
Use: separate the data-only ModelStep computation from the fixed literal
oracle/control-flow semantics. The safeguard is part of execution, not a
contract imposed on the model callback. Concrete ModelStep is supplied by
AlgorithmModel; the generic executor is also useful for proving global
convergence independently of the model and window policy.
Source: the displayed XR pseudocode, including its single rejected probe.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Raw data-only ModelStep result, before safeguard. -/
structure ModelResult (E : Type*) where
  pairs : List (PairObservation E)
  bounds : SpectralBounds
  direction : E
  fallbackCurvature : ℝ
  pairsBeforeTest : ℕ
  deletedByTest : ℕ

/-- The literal safeguarded model direction. -/
def ModelResult.safeDirection (M : ModelResult E) (S : State E) : E :=
  safeguard S.descentConstant S.normConstant M.fallbackCurvature S.gradient M.direction

/-- ModelStep can change only retained observations and running bounds. -/
def ModelResult.updateState (M : ModelResult E) (S : State E) : State E :=
  { S with pairs := M.pairs, bounds := M.bounds }

/-- A pair is computed using the actual tested endpoint and the current
cached starting value/gradient. -/
def observedTrialPair (f : E → ℝ) (G : E → E) (S : State E) (s : E) :
    PairObservation E where
  step := s
  image := G (S.point + s) - S.gradient
  anchor := S.point
  anchorPairing := 0
  valueDefect := f (S.point + s) - S.value - inner ℝ S.gradient s -
    inner ℝ s (G (S.point + s) - S.gradient) / 2

/-- Append precisely when the observed curvature is strictly positive. -/
def appendPositive (W : List (PairObservation E)) (P : PairObservation E) :
    List (PairObservation E) := by
  classical
  exact if positivePair P then W ++ [P] else W

/-- Complete result of the inner loop; its fields record computed data,
without any acceptance or rate certificate. -/
structure SearchResult (E : Type*) where
  pairs : List (PairObservation E)
  bounds : SpectralBounds
  direction : E
  length : ℝ
  evaluations : ℕ
  firstPairs : ℕ
  firstDeleted : ℕ

/-- Literal one-probe search. If the first trial is rejected, its actual
positive-curvature secant is stored, ModelStep is rerun once, and the trial
length is reset to one. All further rejections use quotient backtracking. -/
def outerSearch (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (sigma : ℝ) (S : State E) : SearchResult E := by
  classical
  let M₀ := model S
  let u₀ := M₀.safeDirection S
  exact if Accepted f sigma S.point S.gradient u₀ 1 then
    ⟨M₀.pairs, M₀.bounds, u₀, 1, 1, M₀.pairsBeforeTest, M₀.deletedByTest⟩
  else
    let P := observedTrialPair f G S u₀
    let S₁ := { M₀.updateState S with pairs := appendPositive M₀.pairs P }
    let M₁ := model S₁
    let u₁ := M₁.safeDirection S₁
    let j := backtrackingIndex f sigma S.point S.gradient u₁
    ⟨M₁.pairs, M₁.bounds, u₁, backtrackingSteps f S.point S.gradient u₁ j,
      j + 2, M₀.pairsBeforeTest, M₀.deletedByTest⟩

/-- Accepted outer update: add the accepted positive-curvature pair,
transport all anchor pairings, cache the genuine endpoint observations,
then apply the original capacity rule using the saved first ModelStep data. -/
def outerAdvance (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (S : State E) : State E := by
  classical
  exact if S.gradient = 0 then S else
    let R := outerSearch model f G P.armijo S
    let s := R.length • R.direction
    let W := appendPositive R.pairs (observedTrialPair f G S s)
    let cap := updateCapacity P dimension S.capacity S.cleanCount R.firstPairs
      R.firstDeleted R.evaluations
    { S with
      point := S.point + s
      value := f (S.point + s)
      gradient := G (S.point + s)
      pairs := W.map (fun pair => pair.transport s)
      bounds := R.bounds
      capacity := cap.1
      cleanCount := cap.2 }

/-- Actual recursive XR outer execution, stopped states remaining fixed. -/
def run (P : Parameters) (dimension : ℕ) (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (S₀ : State E) : ℕ → State E
  | 0 => S₀
  | k + 1 => outerAdvance P dimension model f G (run P dimension model f G S₀ k)

/-- Initialization with the printed safeguard constants. In Euclidean
coordinates the literal algorithm passes `initialStep = ‖G x₀‖∞⁻¹`. -/
def initialState (P : Parameters) (f : E → ℝ) (G : E → E) (x₀ : E)
    (initialStep : ℝ) (bounds : SpectralBounds := none) : State E where
  point := x₀
  value := f x₀
  gradient := G x₀
  pairs := []
  capacity := P.initialCapacity
  cleanCount := 0
  bounds := bounds
  initialStep := initialStep
  descentConstant := P.safeguardMargin * initialStep
  normConstant := initialStep / P.safeguardMargin

/-- Every direction used by the actual one-probe search has the safeguard
inequalities, regardless of which rejected-probe branch was executed. -/
theorem outerSearch_gradientRelated (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant) :
    GradientRelated S.descentConstant S.normConstant S.gradient
      (outerSearch model f G sigma S).direction := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _
  · exact safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _

/-- Literal control flow returns an accepted real trial; its existence is
proved from actual derivatives, not stored as a SearchResult field. -/
theorem outerSearch_accepted (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E)
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (sigma : ℝ) (hsigma : sigma < 1) (S : State E)
    (hc₁ : 0 < S.descentConstant) (hc₂ : S.descentConstant ≤ S.normConstant)
    (hcache : S.gradient = G S.point) (hg : S.gradient ≠ 0) :
    Accepted f sigma S.point S.gradient (outerSearch model f G sigma S).direction
      (outerSearch model f G sigma S).length := by
  classical
  unfold outerSearch
  dsimp only
  split
  · assumption
  · dsimp only
    let M₀ := model S
    let u₀ := M₀.safeDirection S
    let S₁ := { M₀.updateState S with
      pairs := appendPositive M₀.pairs (observedTrialPair f G S u₀) }
    let u₁ := (model S₁).safeDirection S₁
    change Accepted f sigma S.point S.gradient u₁
      (backtrackingLength f sigma S.point S.gradient u₁)
    have hu : GradientRelated S.descentConstant S.normConstant S.gradient u₁ :=
      safeguard_gradientRelated _ _ _ hc₁ hc₂ _ _
    rw [hcache] at hu hg ⊢
    exact (backtrackingIndex_spec f sigma S.point (G S.point) u₁
      (backtracking_terminates f G hF L hL hG _ _ sigma hc₁
        (hc₁.trans_le hc₂) hsigma _ _ hg hu)).1

end
end krylov.XR

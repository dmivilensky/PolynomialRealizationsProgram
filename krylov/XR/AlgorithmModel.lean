import krylov.XR.Execution
import krylov.XR.WindowTest
import krylov.Methods.ProjectedModel
import krylov.Completion.ObservedWindowEstimate

/-!
Article: main_krylov, alg:xr and apH:impl, concrete data-only ModelStep.
Use: bind the actual executor to rank/suffix selection, endpoint-value
diagonal gates, genuine generalized Ritz ranges, running spectral bounds,
the Radau interval, the adequacy floor and the full-window branch.
Source: the displayed pseudocode; the Radau endpoints reuse the proved
physical observed-window completion interval. No unknown Hessian is input.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Completion
open scoped InnerProductSpace BigOperators ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Chronological actual stored steps. -/
def storedSteps (W : List (PairObservation E)) (i : Fin W.length) : E := (W.get i).step

/-- Chronological actual stored gradient differences. -/
def storedImages (W : List (PairObservation E)) (i : Fin W.length) : E := (W.get i).image

/-- Actual observed pairing matrix, in the chronological order of the paper. -/
def storedPairing (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  crossGram (storedSteps W) (storedImages W)

/-- The actual latest-information model. -/
def storedModel (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  latest (storedPairing W)

/-- Observable model-metric split, using the transported cached pairing. -/
def storedSplit (W : List (PairObservation E)) (i : Fin W.length) : ℝ :=
  (W.get i).anchorPairing / storedPairing W i i - 1 / 2

/-- Exact-arithmetic value diagonal with the printed oversized-term gate.
The machine-noise gate removes only zero terms and therefore has no further
effect in this exact-real executor. -/
def storedValueTerm (W : List (PairObservation E)) (i : Fin W.length) : ℝ :=
  let term := 12 * storedSplit W i * (W.get i).valueDefect
  if |term| > storedPairing W i i / 2 then 0 else term

/-- Literal observed corrected model, recomputed at the current anchor. -/
def storedValueModel (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  storedModel W - diagonal (storedValueTerm W)

/-- The corrected Hermitian gate retains the original observed skew part. -/
def correctedWindowPasses (theta : ℝ) (W : List (PairObservation E)) : Prop :=
  ((storedValueModel W).map Complex.ofReal +
    (Complex.I / (theta : ℂ)) • (defect (storedPairing W)).map Complex.ofReal).PosDef

/-- The algorithm uses the value model precisely when it is enabled and
its actual Hermitian test passes. -/
def selectedModel (P : Parameters) (W : List (PairObservation E)) :
    Matrix (Fin W.length) (Fin W.length) ℝ := by
  classical
  exact if P.valuesEnabled = true ∧ correctedWindowPasses P.windowThreshold W
    then storedValueModel W else storedModel W

/-- The genuine rank-cleanup loop always terminates at the empty suffix. -/
theorem exists_independent_suffix (W : List (PairObservation E)) :
    ∃ o : ℕ, o ≤ W.length ∧ LinearIndependent ℝ (storedSteps (W.drop o)) := by
  refine ⟨W.length, le_rfl, ?_⟩
  rw [List.drop_length]
  change LinearIndependent ℝ (fun i : Fin 0 => (([] : List (PairObservation E)).get i).step)
  exact linearIndependent_empty_type

/-- Delete the fewest oldest pairs needed for actual column independence. -/
def rankDeletion (W : List (PairObservation E)) : ℕ := by
  classical
  exact Nat.find (exists_independent_suffix W)

/-- The actual rank-cleaned retained window. -/
def rankWindow (dimension : ℕ) (S : State E) : List (PairObservation E) :=
  let W := retainNewest (min S.capacity dimension) S.pairs
  W.drop (rankDeletion W)

/-- Refutation deletions are capped so that a nonempty window retains its
newest observed pair, exactly as in alg:xr. -/
def modelDeletion (P : Parameters) (W : List (PairObservation E)) : ℕ :=
  min (unrefutedSuffix P.windowThreshold (storedPairing W)) (W.length - 1)

/-- The true generalized Rayleigh quotients of the observed model and
physical Gram matrix. Their extrema are exactly the generalized Ritz range. -/
def observedRayleighValues (W : List (PairObservation E)) : Set ℝ :=
  {r | ∃ c : Fin W.length → ℝ, c ≠ 0 ∧
    r = (c ⬝ᵥ (storedModel W *ᵥ c)) / ‖combine (storedSteps W) c‖ ^ 2}

/-- Actual running-bound update from the extreme generalized Ritz values. -/
def updateBounds (inflation : ℝ) (old : SpectralBounds)
    (W : List (PairObservation E)) : SpectralBounds :=
  let lo := sInf (observedRayleighValues W) / inflation
  let hi := inflation * sSup (observedRayleighValues W)
  some (match old with | none => (lo, hi) | some prior => (min prior.1 lo, max prior.2 hi))

/-- The fallback midpoint is computed from the cached running bounds. -/
def fallbackCurvature (bounds : SpectralBounds) (initialStep : ℝ) : ℝ :=
  match bounds with | none => initialStep⁻¹ | some b => (b.1 + b.2) / 2

/-- Physical matrix of the actual stored steps, for the existing Radau API. -/
def storedStepMatrix {n : ℕ} (W : List (PairObservation (EuclideanSpace ℝ (Fin n)))) :
    Matrix (Fin n) (Fin W.length) ℝ := fun a i => storedSteps W i a

/-- The upper-only Schur consistency endpoint, computed using the current
upper bound. The running inflation gives a strict inverse domain on genuine
positive retained data; the totalized inverse defines off-domain execution. -/
def upperConsistencyCoefficient {n p : ℕ} (s : Fin p → EuclideanSpace ℝ (Fin n))
    (T : Matrix (Fin p) (Fin p) ℝ) (d : EuclideanSpace ℝ (Fin n)) (upper : ℝ) : ℝ :=
  upper - upper ^ 2 *
    (coordinates s d ⬝ᵥ ((upper • crossGram s s - T)⁻¹ *ᵥ coordinates s d)) / ‖d‖ ^ 2

/-- Literal lower shifted-Schur endpoint. Unlike an extremum over an
empty completion set, this retains the numerical interval-emptiness test.
Running Ritz inflation supplies the strict inverse domain on reachable
positive windows. -/
def lowerConsistencyCoefficient {n p : ℕ} (s : Fin p → EuclideanSpace ℝ (Fin n))
    (T : Matrix (Fin p) (Fin p) ℝ) (d : EuclideanSpace ℝ (Fin n)) (lower : ℝ) : ℝ :=
  lower + lower ^ 2 *
    (coordinates s d ⬝ᵥ ((T - lower • crossGram s s)⁻¹ *ᵥ coordinates s d)) / ‖d‖ ^ 2

/-- Literal adequacy floor, including its upper consistency clip. -/
def adequacyFloor (sigma eta upperCoefficient directionNormSq estimate : ℝ) : ℝ :=
  min (max estimate (upperCoefficient * directionNormSq / (2 * (1 - sigma) - eta)))
    (upperCoefficient * directionNormSq)

/-- Concrete midpoint-curvature trial rule from the observed physical
consistency interval, followed by the printed upper-only adequacy floor. -/
def observedTrialCurvature {n : ℕ} (P : Parameters)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (T : Matrix (Fin W.length) (Fin W.length) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (bounds : ℝ × ℝ) : ℝ :=
  let lo := lowerConsistencyCoefficient (storedSteps W) T d bounds.1
  let hi := upperConsistencyCoefficient (storedSteps W) T d bounds.2
  let midpoint := (lo + hi) / 2
  let estimate := (if lo ≤ hi then midpoint else min (max midpoint bounds.1) bounds.2) * ‖d‖ ^ 2
  let upper := upperConsistencyCoefficient (storedSteps W) T d bounds.2
  if 0 < upper then adequacyFloor P.armijo P.adequacyMargin upper (‖d‖ ^ 2) estimate
    else estimate

/-- The literal data-only XR ModelStep. Its result is raw; the actual
executor applies safeguard (G) internally. -/
def algorithmModel {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
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
      let T := selectedModel P W
      let w := modelCoefficients s T S.gradient
      let virtual := S.gradient + combine y w
      let d := conjugacyDirection s y virtual
      if W.length = n ∨ d = 0 then combine s w
      else
        let b := bounds.getD (rho, rho)
        let curvature := observedTrialCurvature P W (storedModel W) d b
        combine s w + (-inner ℝ S.gradient d / curvature) • d
  exact ⟨W, bounds, u, rho, W₀.length, o⟩

/-- Literal initialization uses the infinity norm of the actual initial
gradient, while the execution theorem uses the Euclidean safeguard norm. -/
def algorithmInitialState {n : ℕ} (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds := none) :
    State (EuclideanSpace ℝ (Fin n)) :=
  initialState P f G x₀ (‖WithLp.ofLp (G x₀)‖⁻¹) bounds

/-- The full concrete XR algorithm: all model decisions and oracle
evaluations have now been bound to the displayed data-only computation. -/
def algorithmRun {n : ℕ} (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds := none) :
    ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  run P n (algorithmModel P) f G (algorithmInitialState P f G x₀ bounds)

end
end krylov.XR

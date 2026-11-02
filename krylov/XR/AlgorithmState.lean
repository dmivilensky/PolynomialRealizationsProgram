import krylov.Methods.Windows

/-!
Article: main_krylov, alg:xr, observed state and memory bookkeeping.
Use: retain the actual scalar and gradient observations, including a rejected
probe, rather than an operator supplied to the algorithm.
Source: the displayed XR pseudocode. Lists are chronological (oldest first).
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parameters of the literal XR algorithm. Their admissibility is separate
from their data, so execution also has a meaning outside the theorem domain. -/
structure Parameters where
  initialCapacity : ℕ
  maximumCapacity : ℕ
  cleanPeriod : ℕ
  inflation : ℝ
  windowThreshold : ℝ
  armijo : ℝ
  safeguardMargin : ℝ
  adequacyMargin : ℝ
  valuesEnabled : Bool

/-- The inequalities printed before Theorem XR. -/
def Parameters.Valid (P : Parameters) (dimension : ℕ) : Prop :=
  1 ≤ P.initialCapacity ∧ P.initialCapacity ≤ P.maximumCapacity ∧
  P.maximumCapacity ≤ dimension ∧ 1 ≤ P.cleanPeriod ∧
  1 < P.inflation ∧ 0 < P.windowThreshold ∧
  0 < P.armijo ∧ P.armijo < 1 / 2 ∧
  0 < P.safeguardMargin ∧ P.safeguardMargin < 1 ∧
  0 < P.adequacyMargin ∧ P.adequacyMargin < 1 - 2 * P.armijo

/-- One actual stored secant together with the scalar data needed by XR-F.
The anchor is where the observation was made; `anchorPairing` is transported
when the accepted iterate changes. -/
structure PairObservation (E : Type*) where
  step : E
  image : E
  anchor : E
  anchorPairing : ℝ
  valueDefect : ℝ

/-- Running lower/upper spectral estimates; `none` means not yet set. -/
abbrev SpectralBounds := Option (ℝ × ℝ)

/-- Complete cached outer state. Every gradient and scalar is an actual
oracle observation in the executor; no model Hessian is an input field. -/
structure State (E : Type*) where
  point : E
  value : ℝ
  gradient : E
  pairs : List (PairObservation E)
  capacity : ℕ
  cleanCount : ℕ
  bounds : SpectralBounds
  initialStep : ℝ
  descentConstant : ℝ
  normConstant : ℝ

/-- Actual secant and trapezoid defect at a tested point. This definition is
also used for the first rejected probe. -/
def observePair (f : E → ℝ) (G : E → E) (x s : E) : PairObservation E where
  step := s
  image := G (x + s) - G x
  anchor := x
  anchorPairing := 0
  valueDefect := f (x + s) - f x - inner ℝ (G x) s -
    inner ℝ s (G (x + s) - G x) / 2

/-- Real positive-curvature test used before adding a probe pair. -/
def positivePair (P : PairObservation E) : Prop :=
  0 < inner ℝ P.step P.image

/-- Transport the cached anchor covector after an accepted displacement. -/
def PairObservation.transport (P : PairObservation E) (s : E) : PairObservation E :=
  { P with anchorPairing := P.anchorPairing + inner ℝ P.image s }

/-- Keep the most recent pairs, in their chronological order. -/
def retainNewest (capacity : ℕ) (W : List (PairObservation E)) :
    List (PairObservation E) := W.drop (W.length - capacity)

/-- Conversion to the established latest-information model API. -/
def secantPairs (W : List (PairObservation E)) : List (E × E) :=
  W.map (fun P => (P.step, P.image))

/-- Capacity/clean-counter update after one accepted outer iteration.
`initialPairs` and `initialDeleted` are saved from the first ModelStep,
before a rejected probe can trigger a second ModelStep. -/
def updateCapacity (P : Parameters) (dimension capacity cleanCount initialPairs
    initialDeleted evaluations : ℕ) : ℕ × ℕ :=
  if max 1 ((initialPairs + 1) / 2) ≤ initialDeleted then
    (max P.initialCapacity (capacity / 2), 0)
  else
    let clean := if evaluations = 1 ∧ initialDeleted = 0 ∧
        initialPairs = min capacity dimension then cleanCount + 1 else 0
    if clean = P.cleanPeriod then
      (min (capacity + P.initialCapacity) P.maximumCapacity, 0)
    else (capacity, clean)

/-- Transport does not alter the actual stored secant. -/
theorem transport_secant (P : PairObservation E) (s : E) :
    (P.transport s).step = P.step ∧ (P.transport s).image = P.image := by
  exact ⟨rfl, rfl⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Retention never exceeds the requested capacity. -/
theorem retainNewest_length (capacity : ℕ) (W : List (PairObservation E)) :
    (retainNewest capacity W).length = min capacity W.length := by
  simp only [retainNewest, List.length_drop]
  omega

end
end krylov.XR

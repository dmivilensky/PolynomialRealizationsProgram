import krylov.XR.CorrectedDictionary

/-!
Article: main_krylov, lem:xr-local and XRFC-F, genuine scalar executors.
Use: define the full-memory virtual-correction rule using actual queried
function values and gradients. F uses the exact endpoint-value model in
every virtual correction, without algorithmic gates; XR's gates will be
proved to select this rule on the finite stable branch.
Source: alg:xrfc and the displayed XRFC-F definition, literal actual
observations and exact anchor transport. No trajectory or oracle certificate
is an executor field.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- Exact endpoint-value model before XR's scalar oversized-term gate. -/
def storedExactValueModel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (W : List (PairObservation E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  storedModel W - diagonal (fun i => 12 * storedSplit W i * (W.get i).valueDefect)

/-- XRFC-F uses the exact function-value model at every virtual solve;
ordinary XRFC uses the latest observed pair model. -/
def fullVirtualSelectedModel (P : Parameters) (W : List (PairObservation (EuclideanSpace ℝ (Fin n)))) :
    Matrix (Fin W.length) (Fin W.length) ℝ :=
  if P.valuesEnabled then storedExactValueModel W else storedModel W

/-- Actual full-memory virtual correction from genuine endpoint data. -/
def fullVirtualCorrection (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) :=
  modelVirtualCorrection (storedSteps S.pairs) (fullVirtualSelectedModel P S.pairs) S.gradient

/-- The actual virtual model query with a prescribed observable trial
scalar. Its empty-memory branch matches the displayed initialization. -/
def fullVirtualStep (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (S : State (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) := by
  classical
  exact if S.pairs.length = 0 then trial S • (-S.gradient)
    else fullVirtualCorrection P S + trial S •
      modelDirection (storedSteps S.pairs) (storedImages S.pairs)
        (fullVirtualSelectedModel P S.pairs) S.gradient

/-- Running spectral data of the full-memory virtual executor. The
interval model is always the original latest-information model. -/
def fullVirtualBounds (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) : SpectralBounds :=
  if S.pairs.length = 0 then S.bounds else updateBounds P.inflation S.bounds S.pairs

/-- Literal actual full-memory one-gradient update. Every evaluated pair
is stored, and no function value is queried at a virtual correction. -/
def fullVirtualAdvance (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) : State (EuclideanSpace ℝ (Fin n)) :=
  let u := fullVirtualStep P trial S
  let W := S.pairs ++ [observedTrialPair f G S u]
  let cap := updateCapacity P n S.capacity S.cleanCount S.pairs.length 0 1
  { S with
    point := S.point + u
    value := f (S.point + u)
    gradient := G (S.point + u)
    pairs := W.map (fun a => a.transport u)
    bounds := fullVirtualBounds P S
    capacity := cap.1
    cleanCount := cap.2 }

/-- Genuine scalar full-memory XRFC/XRFC-F execution, with one actual
endpoint value/gradient observation per evaluated step. -/
def fullVirtualRun (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) : ℕ → State (EuclideanSpace ℝ (Fin n))
  | 0 => algorithmInitialState P f G x₀ bounds
  | k + 1 => fullVirtualAdvance P trial f G (fullVirtualRun P trial f G x₀ bounds k)

/-- The unevaluated terminal virtual correction makes no extra query. -/
def fullVirtualOutput (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (N : ℕ) : EuclideanSpace ℝ (Fin n) :=
  let S := fullVirtualRun P trial f G x₀ bounds N
  S.point + fullVirtualCorrection P S

/-- Actual endpoint caches remain exact in the full-memory executor. -/
theorem fullVirtualRun_cache (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    let S := fullVirtualRun P trial f G x₀ bounds k
    S.value = f S.point ∧ S.gradient = G S.point := by
  cases k <;> exact ⟨rfl, rfl⟩

/-- Full-memory pairs are genuine observed secants and endpoint defects,
with exact transported current-anchor covectors at every finite prefix. -/
theorem fullVirtualRun_faithful (P : Parameters) (trial : State (EuclideanSpace ℝ (Fin n)) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (fullVirtualRun P trial f G x₀ bounds k).pairs,
      PairFaithful f G (fullVirtualRun P trial f G x₀ bounds k).point a := by
  induction k with
  | zero => simp [fullVirtualRun, algorithmInitialState, initialState]
  | succ k ih =>
    let S := fullVirtualRun P trial f G x₀ bounds k
    let u := fullVirtualStep P trial S
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    apply PairFaithful.transport
    rcases List.mem_append.mp hb with hb | hb
    · exact ih b hb
    · have hc := fullVirtualRun_cache P trial f G x₀ bounds k
      have hn := observedTrialPair_faithful f G S hc.1 hc.2 u
      simpa only [List.mem_singleton.mp hb] using hn

end
end krylov.XR

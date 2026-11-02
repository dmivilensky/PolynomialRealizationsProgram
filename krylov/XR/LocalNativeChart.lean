import krylov.XR.LocalHistoryPairs
import krylov.XR.XRFCReplay

/-!
Article: main_krylov, lem:xr-local, literal native endpoint-state chart.
Use: reconstruct the actual full-capacity finite XR state from retained
endpoint data, including running Ritz bounds and initialization. The
primitive trial chart is exactly the algorithm's computed trial, not a
smooth surrogate. Source: literal state definitions and exact chronological
append/anchor transport; no trajectory or decision certificate is a field.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- Remove only the last endpoint of a chronological finite chart. -/
def trimEndpointChart {E : Type*} {k : ℕ} (C : EndpointChart E (k + 1)) : EndpointChart E k :=
  (Fin.init C.1, Fin.init C.2.1, Fin.init C.2.2)

/-- The literal running Ritz bounds reconstructed from all observed
prefixes. The source always uses the ordinary latest model for this data. -/
def endpointRunningBounds (P : Parameters) (initial : SpectralBounds) :
    (k : ℕ) → EndpointChart (EuclideanSpace ℝ (Fin n)) k → SpectralBounds
  | 0, _ => initial
  | k + 1, C =>
    let previous := trimEndpointChart C
    let old := endpointRunningBounds P initial k previous
    if k = 0 then old else updateBounds P.inflation old (endpointObservations previous)

/-- The literal full-memory native state chart before the terminal
correction. During its first n queries capacity is full and the clean
counter has not yet completed a full-window iteration. -/
def endpointNativeState (P : Parameters) (initial : SpectralBounds) {k : ℕ}
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k) : State (EuclideanSpace ℝ (Fin n)) :=
  let alpha := ‖WithLp.ofLp (C.2.2 0)‖⁻¹
  { point := C.1 (Fin.last k)
    value := C.2.1 (Fin.last k)
    gradient := C.2.2 (Fin.last k)
    pairs := endpointObservations C
    capacity := P.initialCapacity
    cleanCount := 0
    bounds := endpointRunningBounds P initial k C
    initialStep := alpha
    descentConstant := P.safeguardMargin * alpha
    normConstant := alpha / P.safeguardMargin }

/-- The genuine algorithmic trial as a function of its actual endpoint
observations, including its real running spectral estimates and floor. -/
def endpointComputedTrial (P : Parameters) (initial : SpectralBounds) (k : ℕ)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k) : ℝ :=
  algorithmTrialParameter P (endpointNativeState P initial C)

/-- Before its first full-window correction, the original full-capacity
counter update preserves exactly capacity n and clean counter zero. -/
theorem updateCapacity_full_prefix (P : Parameters) (hinit : P.initialCapacity = n)
    (hmax : P.maximumCapacity = n) (k : ℕ) (hk : k < n) :
    updateCapacity P n P.initialCapacity 0 k 0 1 = (P.initialCapacity, 0) := by
  have hclean : k ≠ min P.initialCapacity n := by
    rw [hinit, min_self]
    omega
  have hdelete : ¬max 1 ((k + 1) / 2) ≤ 0 := by omega
  simp only [updateCapacity, ite_eq_right hdelete, hclean, and_false, ite_false]
  split_ifs
  · rw [hinit, hmax, min_eq_right (by omega)]
  · rfl

/-- The native state reconstructed at the initial endpoint is the actual
algorithm initialization, including the prescribed infinity-norm scalar. -/
theorem endpointNativeState_initial (P : Parameters) (initial : SpectralBounds)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) :
    endpointNativeState P initial (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P initial) f G x₀ 0) =
      algorithmInitialState P f G x₀ initial := by
  simp only [endpointNativeState, endpointFunctionRun, endpointObservations, List.ofFn_zero,
    endpointRunningBounds, algorithmInitialState, initialState]

/-- One true endpoint append is exactly the native full-memory advance,
with the original actually computed trial and running-bound update. -/
theorem endpointNativeState_advance (P : Parameters) (initial : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n) {k : ℕ} (hk : k < n)
    (C : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) :
    let S := endpointNativeState P initial C
    let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P initial k) C
    endpointNativeState P initial (extendEndpointChart C x (f x, G x)) =
      fullVirtualAdvance P (algorithmTrialParameter P) f G S := by
  let S := endpointNativeState P initial C
  let x := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P initial k) C
  let u := fullVirtualStep P (algorithmTrialParameter P) S
  have hx : S.point + u = x := fullVirtualStep_endpoint P C S (algorithmTrialParameter P)
    (endpointComputedTrial P initial k) rfl rfl rfl rfl
  have hu : fullVirtualStep P (algorithmTrialParameter P) S = x - C.1 (Fin.last k) := by
    change u = _
    change C.1 (Fin.last k) + u = x at hx
    rw [← hx]
    abel
  have hnew : observedTrialPair f G S u = endpointNewObservation C x (f x, G x) := by
    dsimp only [observedTrialPair, endpointNewObservation]
    have hu' : u = x - C.1 (Fin.last k) := hu
    rw [hx, hu']
    rfl
  have htrim : trimEndpointChart (extendEndpointChart C x (f x, G x)) = C := by
    simp only [trimEndpointChart, extendEndpointChart, Fin.init_snoc, Prod.mk.eta]
  have hb : endpointRunningBounds P initial (k + 1) (extendEndpointChart C x (f x, G x)) =
      fullVirtualBounds P S := by
    rw [endpointRunningBounds, htrim]
    unfold fullVirtualBounds
    change (if k = 0 then _ else _) =
      if (endpointObservations C).length = 0 then _ else _
    rw [endpointObservations_length]
    rfl
  dsimp only
  change endpointNativeState P initial (extendEndpointChart C x (f x, G x)) =
    fullVirtualAdvance P (algorithmTrialParameter P) f G S
  have hc : updateCapacity P n S.capacity S.cleanCount S.pairs.length 0 1 = (P.initialCapacity, 0) := by
    change updateCapacity P n P.initialCapacity 0 (endpointObservations C).length 0 1 = _
    rw [endpointObservations_length]
    exact updateCapacity_full_prefix P hinit hmax k hk
  unfold fullVirtualAdvance
  dsimp only
  rw [hx, hnew, hu, hc]
  have hp := endpointObservations_extend C x (f x, G x)
  unfold endpointNativeState
  rw [hp, hb]
  dsimp only [S, endpointNativeState]
  have hzero : (extendEndpointChart C x (f x, G x)).2.2 0 = C.2.2 0 := by
    exact Fin.snoc_apply_zero (n := k + 1)
      (α := fun _ : Fin (k + 2) => EuclideanSpace ℝ (Fin n)) (G x) C.2.2
  rw [hzero]
  simp only [extendEndpointChart, Fin.snoc_last]

/-- The genuine list-based scalar XRFC/F execution and the actual smooth
endpoint program coincide through the entire first full-memory cycle.
The trial is exactly XR's own computed data rule on both sides. -/
theorem fullVirtualRun_eq_endpointNativeState (P : Parameters) (initial : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k ≤ n) :
    fullVirtualRun P (algorithmTrialParameter P) f G x₀ initial k =
      endpointNativeState P initial
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P initial) f G x₀ k) := by
  induction k with
  | zero => exact (endpointNativeState_initial P initial f G x₀).symm
  | succ k ih =>
    rw [fullVirtualRun, ih (by omega), endpointFunctionRun]
    exact (endpointNativeState_advance P initial hinit hmax (by omega) _ f G).symm

end
end krylov.XR

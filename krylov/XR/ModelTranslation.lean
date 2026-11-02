import krylov.XR.ExecutionTranslation
import krylov.Methods.WindowCoordinates
import krylov.Methods.DirectionReindex

/-!
Article: main_krylov, alg:xr and thm:XR, translation of ModelStep.
Use: verify that the literal rank cleanup, Hermitian suffix selection,
endpoint-value gate, generalized Ritz extrema and Schur trial rule depend
only on observed differences and transported covectors. Absolute anchors
are retained in memory, but do not enter any model computation.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace ComplexOrder
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem storedSteps_shift (b : E) (W : List (PairObservation E)) :
    storedSteps (W.map (PairObservation.shift b)) =
      storedSteps W ∘ finCongr (List.length_map ..) := by
  funext i
  change ((W.map (PairObservation.shift b))[i.val]).step = _
  rw [List.getElem_map]
  rfl

omit [InnerProductSpace ℝ E] in
theorem storedImages_shift (b : E) (W : List (PairObservation E)) :
    storedImages (W.map (PairObservation.shift b)) =
      storedImages W ∘ finCongr (List.length_map ..) := by
  funext i
  change ((W.map (PairObservation.shift b))[i.val]).image = _
  rw [List.getElem_map]
  rfl

theorem storedPairing_shift (b : E) (W : List (PairObservation E)) :
    storedPairing (W.map (PairObservation.shift b)) =
      (storedPairing W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  rw [storedPairing, storedSteps_shift, storedImages_shift]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem latest_finCongr {a c : ℕ} (h : a = c) (M : Matrix (Fin c) (Fin c) ℝ) :
    latest (M.submatrix (finCongr h) (finCongr h)) =
      (latest M).submatrix (finCongr h) (finCongr h) := by
  subst c
  rfl

theorem storedModel_shift (b : E) (W : List (PairObservation E)) :
    storedModel (W.map (PairObservation.shift b)) =
      (storedModel W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  rw [storedModel, storedPairing_shift, latest_finCongr]
  rfl

theorem storedSplit_shift (b : E) (W : List (PairObservation E))
    (i : Fin (W.map (PairObservation.shift b)).length) :
    storedSplit (W.map (PairObservation.shift b)) i =
      storedSplit W (finCongr (List.length_map ..) i) := by
  unfold storedSplit
  rw [storedPairing_shift]
  change ((W.map (PairObservation.shift b))[i.val]).anchorPairing / _ - _ = _
  rw [List.getElem_map]
  rfl

theorem storedValueTerm_shift (b : E) (W : List (PairObservation E))
    (i : Fin (W.map (PairObservation.shift b)).length) :
    storedValueTerm (W.map (PairObservation.shift b)) i =
      storedValueTerm W (finCongr (List.length_map ..) i) := by
  classical
  unfold storedValueTerm
  simp only [storedSplit_shift, storedPairing_shift, List.get_eq_getElem, List.getElem_map]
  rfl

theorem storedValueModel_shift (b : E) (W : List (PairObservation E)) :
    storedValueModel (W.map (PairObservation.shift b)) =
      (storedValueModel W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  rw [storedValueModel, storedModel_shift]
  ext i j
  simp only [Matrix.sub_apply, Matrix.submatrix_apply, storedValueModel]
  congr 1
  by_cases hij : i = j
  · subst j
    simp only [diagonal_apply_eq, storedValueTerm_shift]
  · rw [diagonal_apply_ne _ hij,
      diagonal_apply_ne _ ((finCongr (List.length_map ..)).injective.ne hij)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem corrected_test_finCongr {a c : ℕ} (h : a = c) (theta : ℝ)
    (T M : Matrix (Fin c) (Fin c) ℝ) :
    ((T.submatrix (finCongr h) (finCongr h)).map Complex.ofReal +
      (Complex.I / (theta : ℂ)) •
        (defect (M.submatrix (finCongr h) (finCongr h))).map Complex.ofReal).PosDef ↔
    (T.map Complex.ofReal +
      (Complex.I / (theta : ℂ)) • (defect M).map Complex.ofReal).PosDef := by
  subst c
  rfl

theorem correctedWindowPasses_shift (b : E) (theta : ℝ) (W : List (PairObservation E)) :
    correctedWindowPasses theta (W.map (PairObservation.shift b)) ↔ correctedWindowPasses theta W := by
  unfold correctedWindowPasses
  rw [storedValueModel_shift, storedPairing_shift, corrected_test_finCongr]

theorem selectedModel_shift (b : E) (P : Parameters) (W : List (PairObservation E)) :
    selectedModel P (W.map (PairObservation.shift b)) =
      (selectedModel P W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  classical
  unfold selectedModel
  simp only [correctedWindowPasses_shift]
  split <;> simp only [storedValueModel_shift, storedModel_shift]

theorem storedSteps_shift_independent (b : E) (W : List (PairObservation E)) :
    LinearIndependent ℝ (storedSteps (W.map (PairObservation.shift b))) ↔
      LinearIndependent ℝ (storedSteps W) := by
  rw [storedSteps_shift]
  exact linearIndependent_equiv (finCongr (List.length_map ..))

omit [InnerProductSpace ℝ E] in
theorem shift_drop (b : E) (W : List (PairObservation E)) (i : ℕ) :
    (W.map (PairObservation.shift b)).drop i = (W.drop i).map (PairObservation.shift b) :=
  List.map_drop.symm

theorem rankDeletion_shift (b : E) (W : List (PairObservation E)) :
    rankDeletion (W.map (PairObservation.shift b)) = rankDeletion W := by
  classical
  unfold rankDeletion
  apply Nat.find_congr'
  intro i
  have hd := storedSteps_shift_independent b (W.drop i)
  rw [List.map_drop] at hd
  simpa only [List.length_map] using and_congr Iff.rfl hd

theorem rankWindow_shift (b : E) (dimension : ℕ) (S : State E) :
    rankWindow dimension (S.shift b) = (rankWindow dimension S).map (PairObservation.shift b) := by
  simp only [rankWindow, State.shift, retainNewest, List.length_map, shift_drop,
    rankDeletion_shift]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem unrefutedSuffix_finCongr {a c : ℕ} (h : a = c) (theta : ℝ)
    (M : Matrix (Fin c) (Fin c) ℝ) :
    unrefutedSuffix theta (M.submatrix (finCongr h) (finCongr h)) = unrefutedSuffix theta M := by
  subst c
  rfl

theorem modelDeletion_shift (b : E) (P : Parameters) (W : List (PairObservation E)) :
    modelDeletion P (W.map (PairObservation.shift b)) = modelDeletion P W := by
  rw [modelDeletion, storedPairing_shift, unrefutedSuffix_finCongr, List.length_map]
  rfl

theorem rayleighValues_finCongr {a c : ℕ} (h : a = c) (s : Fin c → E)
    (T : Matrix (Fin c) (Fin c) ℝ) :
    {r : ℝ | ∃ v : Fin a → ℝ, v ≠ 0 ∧
      r = (v ⬝ᵥ ((T.submatrix (finCongr h) (finCongr h)) *ᵥ v)) /
        ‖combine (s ∘ finCongr h) v‖ ^ 2} =
    {r : ℝ | ∃ v : Fin c → ℝ, v ≠ 0 ∧ r = (v ⬝ᵥ (T *ᵥ v)) / ‖combine s v‖ ^ 2} := by
  subst c
  rfl

theorem observedRayleighValues_shift (b : E) (W : List (PairObservation E)) :
    observedRayleighValues (W.map (PairObservation.shift b)) = observedRayleighValues W := by
  unfold observedRayleighValues
  rw [storedModel_shift, storedSteps_shift, rayleighValues_finCongr]

theorem updateBounds_shift (b : E) (inflation : ℝ) (old : SpectralBounds)
    (W : List (PairObservation E)) :
    updateBounds inflation old (W.map (PairObservation.shift b)) = updateBounds inflation old W := by
  simp only [updateBounds, observedRayleighValues_shift]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem consistency_finCongr {n a c : ℕ} (h : a = c)
    (s : Fin c → EuclideanSpace ℝ (Fin n)) (T : Matrix (Fin c) (Fin c) ℝ)
    (d : EuclideanSpace ℝ (Fin n)) (bound : ℝ) :
    upperConsistencyCoefficient (s ∘ finCongr h)
        (T.submatrix (finCongr h) (finCongr h)) d bound = upperConsistencyCoefficient s T d bound ∧
    lowerConsistencyCoefficient (s ∘ finCongr h)
        (T.submatrix (finCongr h) (finCongr h)) d bound = lowerConsistencyCoefficient s T d bound := by
  subst c
  exact ⟨rfl, rfl⟩

theorem observedTrialCurvature_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (d : EuclideanSpace ℝ (Fin n)) (bounds : ℝ × ℝ) :
    observedTrialCurvature P (W.map (PairObservation.shift b))
      (storedModel (W.map (PairObservation.shift b))) d bounds =
      observedTrialCurvature P W (storedModel W) d bounds := by
  simp only [observedTrialCurvature, storedSteps_shift, storedModel_shift,
    (consistency_finCongr _ _ _ _ _).1, (consistency_finCongr _ _ _ _ _).2]

/-- A genuine physical solve and direction ignore the sole finite-length
cast introduced by mapping stored anchors. -/
theorem modelPhysicalData_finCongr {a c : ℕ} (h : a = c) (s y : Fin c → E)
    (T : Matrix (Fin c) (Fin c) ℝ) (g : E) :
    combine (s ∘ finCongr h)
        (modelCoefficients (s ∘ finCongr h) (T.submatrix (finCongr h) (finCongr h)) g) =
      combine s (modelCoefficients s T g) ∧
    conjugacyDirection (s ∘ finCongr h) (y ∘ finCongr h)
        (g + combine (y ∘ finCongr h)
          (modelCoefficients (s ∘ finCongr h) (T.submatrix (finCongr h) (finCongr h)) g)) =
      conjugacyDirection s y (g + combine y (modelCoefficients s T g)) := by
  subst c
  exact ⟨rfl, rfl⟩

/-- The literal direction formula after its retained window and updated
spectral bounds have been computed. -/
def computedWindowStep {n : ℕ} (P : Parameters)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n)) (initial : ℝ) (bounds : SpectralBounds) :
    EuclideanSpace ℝ (Fin n) := by
  classical
  let rho := fallbackCurvature bounds initial
  exact if W.length = 0 then
    -(match bounds with | none => initial | some b => 2 / (b.1 + b.2)) • g
  else
    let s := storedSteps W
    let y := storedImages W
    let T := selectedModel P W
    let w := modelCoefficients s T g
    let d := conjugacyDirection s y (g + combine y w)
    if W.length = n ∨ d = 0 then combine s w
    else combine s w + (-inner ℝ g d /
      observedTrialCurvature P W (storedModel W) d (bounds.getD (rho, rho))) • d

theorem computedWindowStep_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n)) (initial : ℝ) (bounds : SpectralBounds) :
    computedWindowStep P (W.map (PairObservation.shift b)) g initial bounds =
      computedWindowStep P W g initial bounds := by
  classical
  unfold computedWindowStep
  dsimp only
  simp only [List.length_map]
  by_cases hz : W.length = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false]
    rw [storedSteps_shift, storedImages_shift, selectedModel_shift]
    rw [(modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
      (selectedModel P W) g).2,
      (modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
        (selectedModel P W) g).1]
    simp only [observedTrialCurvature_shift]

/-- Every branch of the concrete observed ModelStep is translation
invariant, including singular totalized solves and rejected-probe memory. -/
theorem algorithmModel_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    algorithmModel P (S.shift b) = (algorithmModel P S).shift b := by
  classical
  let W (S : State (EuclideanSpace ℝ (Fin n))) :=
    (rankWindow n S).drop (modelDeletion P (rankWindow n S))
  have hw : W (S.shift b) = (W S).map (PairObservation.shift b) := by
    simp only [W, rankWindow_shift, modelDeletion_shift, shift_drop]
  let B (S : State (EuclideanSpace ℝ (Fin n))) :=
    if (W S).length = 0 then S.bounds else updateBounds P.inflation S.bounds (W S)
  have hb : B (S.shift b) = B S := by
    simp only [B, hw, List.length_map, updateBounds_shift,
      show (S.shift b).bounds = S.bounds from rfl]
  change (⟨W (S.shift b), B (S.shift b),
      computedWindowStep P (W (S.shift b)) (S.shift b).gradient (S.shift b).initialStep (B (S.shift b)),
      fallbackCurvature (B (S.shift b)) (S.shift b).initialStep,
      (rankWindow n (S.shift b)).length, modelDeletion P (rankWindow n (S.shift b))⟩ : ModelResult _) =
    (⟨W S, B S, computedWindowStep P (W S) S.gradient S.initialStep (B S),
      fallbackCurvature (B S) S.initialStep, (rankWindow n S).length,
      modelDeletion P (rankWindow n S)⟩ : ModelResult _).shift b
  rw [hw, hb, rankWindow_shift, modelDeletion_shift]
  simp only [computedWindowStep_shift, List.length_map, State.shift, ModelResult.shift]

theorem algorithmInitialState_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) :
    algorithmInitialState P (fun x => f (x - b)) (fun x => G (x - b)) b bounds =
      (algorithmInitialState P f G 0 bounds).shift b := by
  simp only [algorithmInitialState, initialState, State.shift, sub_self, zero_add,
    List.map_nil]

/-- Literal unsafeguarded executions are independent of the coordinate
origin; all rejected probes and backtracking indices are included. -/
theorem rawAlgorithmRun_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds) (k : ℕ) :
    rawAlgorithmRun P (fun x => f (x - b)) (fun x => G (x - b)) b bounds k =
      (rawAlgorithmRun P f G 0 bounds k).shift b := by
  unfold rawAlgorithmRun
  rw [algorithmInitialState_shift]
  exact rawRun_shift b P n (algorithmModel P) (algorithmModel_shift b P) f G _ k

end
end krylov.XR

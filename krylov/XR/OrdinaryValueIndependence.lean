import krylov.XR.ModelTranslation
import krylov.XR.LocalNativeChart

/-!
Article: main_krylov, lem:xr-local, ordinary XR ignores scalar samples.
Use: the literal ordinary rank cleanup, Hermitian suffix, Ritz cache,
Schur endpoints and trial scalar depend only on points and gradients.
This exact identity permits smooth operator input charts without assuming
an output or trial regularity certificate for the actual executor.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Erase only the scalar trapezoid observation, retaining real secants. -/
def PairObservation.eraseValue (a : PairObservation E) : PairObservation E :=
  { a with valueDefect := 0 }

/-- Erase scalar samples while preserving every ordinary algorithm input. -/
def State.eraseValue (S : State E) : State E :=
  { S with value := 0, pairs := S.pairs.map PairObservation.eraseValue }

def ModelResult.eraseValue (M : ModelResult E) : ModelResult E :=
  { M with pairs := M.pairs.map PairObservation.eraseValue }

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem storedSteps_eraseValue (W : List (PairObservation E)) :
    storedSteps (W.map PairObservation.eraseValue) =
      storedSteps W ∘ finCongr (List.length_map ..) := by
  funext i
  change ((W.map PairObservation.eraseValue)[i.val]).step = _
  rw [List.getElem_map]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem storedImages_eraseValue (W : List (PairObservation E)) :
    storedImages (W.map PairObservation.eraseValue) =
      storedImages W ∘ finCongr (List.length_map ..) := by
  funext i
  change ((W.map PairObservation.eraseValue)[i.val]).image = _
  rw [List.getElem_map]
  rfl

theorem storedPairing_eraseValue (W : List (PairObservation E)) :
    storedPairing (W.map PairObservation.eraseValue) =
      (storedPairing W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  rw [storedPairing, storedSteps_eraseValue, storedImages_eraseValue]
  rfl

theorem storedModel_eraseValue (W : List (PairObservation E)) :
    storedModel (W.map PairObservation.eraseValue) =
      (storedModel W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  rw [storedModel, storedPairing_eraseValue, latest_finCongr]
  rfl

theorem selectedModel_eraseValue (P : Parameters) (hoff : P.valuesEnabled = false)
    (W : List (PairObservation E)) :
    selectedModel P (W.map PairObservation.eraseValue) =
      (selectedModel P W).submatrix (finCongr (List.length_map ..)) (finCongr (List.length_map ..)) := by
  classical
  simp only [selectedModel, hoff, Bool.false_eq_true, false_and, ite_false, storedModel_eraseValue]

theorem rankDeletion_eraseValue (W : List (PairObservation E)) :
    rankDeletion (W.map PairObservation.eraseValue) = rankDeletion W := by
  classical
  unfold rankDeletion
  apply Nat.find_congr'
  intro i
  have hd : LinearIndependent ℝ (storedSteps ((W.drop i).map PairObservation.eraseValue)) ↔
      LinearIndependent ℝ (storedSteps (W.drop i)) := by
    rw [storedSteps_eraseValue]
    exact linearIndependent_equiv (finCongr (List.length_map ..))
  rw [List.map_drop] at hd
  simpa only [List.length_map] using and_congr Iff.rfl hd

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem eraseValue_drop (W : List (PairObservation E)) (i : ℕ) :
    (W.map PairObservation.eraseValue).drop i = (W.drop i).map PairObservation.eraseValue :=
  List.map_drop.symm

theorem rankWindow_eraseValue (dimension : ℕ) (S : State E) :
    rankWindow dimension S.eraseValue = (rankWindow dimension S).map PairObservation.eraseValue := by
  simp only [rankWindow, State.eraseValue, retainNewest, List.length_map, eraseValue_drop,
    rankDeletion_eraseValue]

theorem modelDeletion_eraseValue (P : Parameters) (W : List (PairObservation E)) :
    modelDeletion P (W.map PairObservation.eraseValue) = modelDeletion P W := by
  rw [modelDeletion, storedPairing_eraseValue, unrefutedSuffix_finCongr, List.length_map]
  rfl

theorem observedRayleighValues_eraseValue (W : List (PairObservation E)) :
    observedRayleighValues (W.map PairObservation.eraseValue) = observedRayleighValues W := by
  unfold observedRayleighValues
  rw [storedModel_eraseValue, storedSteps_eraseValue, rayleighValues_finCongr]

theorem updateBounds_eraseValue (inflation : ℝ) (old : SpectralBounds)
    (W : List (PairObservation E)) :
    updateBounds inflation old (W.map PairObservation.eraseValue) = updateBounds inflation old W := by
  simp only [updateBounds, observedRayleighValues_eraseValue]

theorem observedTrialCurvature_eraseValue {n : ℕ} (P : Parameters)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (d : EuclideanSpace ℝ (Fin n)) (bounds : ℝ × ℝ) :
    observedTrialCurvature P (W.map PairObservation.eraseValue)
      (storedModel (W.map PairObservation.eraseValue)) d bounds =
      observedTrialCurvature P W (storedModel W) d bounds := by
  simp only [observedTrialCurvature, storedSteps_eraseValue, storedModel_eraseValue,
    (consistency_finCongr _ _ _ _ _).1, (consistency_finCongr _ _ _ _ _).2]

theorem computedWindowStep_eraseValue {n : ℕ} (P : Parameters) (hoff : P.valuesEnabled = false)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n)) (initial : ℝ) (bounds : SpectralBounds) :
    computedWindowStep P (W.map PairObservation.eraseValue) g initial bounds =
      computedWindowStep P W g initial bounds := by
  classical
  unfold computedWindowStep
  dsimp only
  simp only [List.length_map]
  by_cases hz : W.length = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false]
    rw [storedSteps_eraseValue, storedImages_eraseValue, selectedModel_eraseValue P hoff]
    rw [(modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
      (selectedModel P W) g).2,
      (modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
        (selectedModel P W) g).1]
    simp only [observedTrialCurvature_eraseValue]

theorem algorithmModel_eraseValue {n : ℕ} (P : Parameters) (hoff : P.valuesEnabled = false)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    algorithmModel P S.eraseValue = (algorithmModel P S).eraseValue := by
  classical
  let W (S : State (EuclideanSpace ℝ (Fin n))) :=
    (rankWindow n S).drop (modelDeletion P (rankWindow n S))
  have hw : W S.eraseValue = (W S).map PairObservation.eraseValue := by
    simp only [W, rankWindow_eraseValue, modelDeletion_eraseValue, List.map_drop]
  let B (S : State (EuclideanSpace ℝ (Fin n))) :=
    if (W S).length = 0 then S.bounds else updateBounds P.inflation S.bounds (W S)
  have hb : B S.eraseValue = B S := by
    simp only [B, hw, List.length_map, updateBounds_eraseValue,
      show S.eraseValue.bounds = S.bounds from rfl]
  change (⟨W S.eraseValue, B S.eraseValue,
      computedWindowStep P (W S.eraseValue) S.eraseValue.gradient S.eraseValue.initialStep (B S.eraseValue),
      fallbackCurvature (B S.eraseValue) S.eraseValue.initialStep,
      (rankWindow n S.eraseValue).length, modelDeletion P (rankWindow n S.eraseValue)⟩ : ModelResult _) =
    (⟨W S, B S, computedWindowStep P (W S) S.gradient S.initialStep (B S),
      fallbackCurvature (B S) S.initialStep, (rankWindow n S).length,
      modelDeletion P (rankWindow n S)⟩ : ModelResult _).eraseValue
  rw [hw, hb, rankWindow_eraseValue, modelDeletion_eraseValue]
  simp only [computedWindowStep_eraseValue P hoff, List.length_map, State.eraseValue, ModelResult.eraseValue]

/-- The genuine ordinary trial scalar ignores erased scalar samples,
including all rank, suffix, cache, Schur and floor computations. -/
theorem algorithmTrialParameter_eraseValue {n : ℕ} (P : Parameters)
    (hoff : P.valuesEnabled = false) (S : State (EuclideanSpace ℝ (Fin n))) :
    algorithmTrialParameter P S.eraseValue = algorithmTrialParameter P S := by
  classical
  have hdir (W : List (PairObservation (EuclideanSpace ℝ (Fin n)))) :
      modelDirection (storedSteps (W.map PairObservation.eraseValue))
        (storedImages (W.map PairObservation.eraseValue))
        (selectedModel P (W.map PairObservation.eraseValue)) S.gradient =
      modelDirection (storedSteps W) (storedImages W) (selectedModel P W) S.gradient := by
    unfold modelDirection modelVirtualGradient
    rw [storedSteps_eraseValue, storedImages_eraseValue, selectedModel_eraseValue P hoff]
    exact (modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
      (selectedModel P W) S.gradient).2
  unfold algorithmTrialParameter
  rw [algorithmModel_eraseValue P hoff]
  dsimp only [ModelResult.eraseValue, State.eraseValue]
  simp only [List.length_map, hdir]
  unfold modelTrialLength
  rw [hdir, observedTrialCurvature_eraseValue]

/-- A canonical ordinary endpoint state ignores cached scalar observations
once its points and gradients have been fixed. -/
theorem endpointObservations_eraseValue_congr {k : ℕ} (C D : EndpointChart E k)
    (hp : C.1 = D.1) (hg : C.2.2 = D.2.2) :
    (endpointObservations C).map PairObservation.eraseValue =
      (endpointObservations D).map PairObservation.eraseValue := by
  simp only [endpointObservations, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, PairObservation.eraseValue, endpointStep, endpointImage, hp, hg]

theorem endpointRunningBounds_value_congr {n k : ℕ} (P : Parameters) (initial : SpectralBounds)
    (C D : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (hp : C.1 = D.1) (hg : C.2.2 = D.2.2) :
    endpointRunningBounds P initial k C = endpointRunningBounds P initial k D := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have htrimP : (trimEndpointChart C).1 = (trimEndpointChart D).1 := congrArg Fin.init hp
    have htrimG : (trimEndpointChart C).2.2 = (trimEndpointChart D).2.2 := congrArg Fin.init hg
    have he := endpointObservations_eraseValue_congr (trimEndpointChart C) (trimEndpointChart D) htrimP htrimG
    have hu : ∀ old, updateBounds P.inflation old (endpointObservations (trimEndpointChart C)) =
        updateBounds P.inflation old (endpointObservations (trimEndpointChart D)) := by
      intro old
      rw [←updateBounds_eraseValue, he, updateBounds_eraseValue]
    simp only [endpointRunningBounds, ih _ _ htrimP htrimG, hu]

theorem endpointNativeState_eraseValue_congr {n k : ℕ} (P : Parameters) (initial : SpectralBounds)
    (C D : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (hp : C.1 = D.1) (hg : C.2.2 = D.2.2) :
    (endpointNativeState P initial C).eraseValue = (endpointNativeState P initial D).eraseValue := by
  have hb := endpointRunningBounds_value_congr P initial C D hp hg
  have he := endpointObservations_eraseValue_congr C D hp hg
  simp only [endpointNativeState, State.eraseValue, hp, hg, hb, he]

theorem endpointComputedTrial_value_congr {n k : ℕ} (P : Parameters) (hoff : P.valuesEnabled = false)
    (initial : SpectralBounds) (C D : EndpointChart (EuclideanSpace ℝ (Fin n)) k)
    (hp : C.1 = D.1) (hg : C.2.2 = D.2.2) :
    endpointComputedTrial P initial k C = endpointComputedTrial P initial k D := by
  unfold endpointComputedTrial
  rw [←algorithmTrialParameter_eraseValue P hoff,
    endpointNativeState_eraseValue_congr P initial C D hp hg, algorithmTrialParameter_eraseValue P hoff]

end
end krylov.XR

import krylov.XR.PracticalQuadraticAlgorithm
import krylov.XR.QuadraticTranslation

/-!
# Translation of the actual fresh-secant trajectory

Theorem 7.1 (`thm:XR`): all retained steps, cache transports, fresh secant
quotients, model queries and raw outer states commute with translation.
The resulting theorem covers arbitrary initial points, rather than an
assumed reference trajectory. Source: affine translation of observations.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Reference
open scoped InnerProductSpace
set_option maxHeartbeats 800000

/-- The fresh quotient and its fallback depend only on difference data. -/
theorem freshCurvature_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : E) (previous : ℝ) (W : List (PairObservation E)) :
    freshCurvature previous (W.map (PairObservation.shift b)) = freshCurvature previous W := by
  classical
  unfold freshCurvature
  rw [List.getLast?_map]
  cases W.getLast? <;> rfl

/-- The finite index cast in translated observations changes no trial. -/
theorem modelTrialStep_finCongr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a c : ℕ} (h : a = c) (s y : Fin c → E) (T : Matrix (Fin c) (Fin c) ℝ)
    (g : E) (curvature : ℝ) :
    modelTrialStep (s ∘ finCongr h) (y ∘ finCongr h)
      (T.submatrix (finCongr h) (finCongr h)) g curvature = modelTrialStep s y T g curvature := by
  subst c
  rfl

/-- The practical window step with its fresh scalar already computed. -/
def computedPracticalWindowStep {n : ℕ} (P : Parameters)
    (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n)) (rho : ℝ) : EuclideanSpace ℝ (Fin n) := by
  classical
  exact if W.length = 0 then -(rho⁻¹) • g else
    let s := storedSteps W
    let y := storedImages W
    let T := selectedModel P W
    if W.length = n then modelVirtualCorrection s T g else
      modelTrialStep s y T g (rho * ‖modelDirection s y T g‖ ^ 2)

/-- Absolute anchors do not enter any branch of the practical window step. -/
theorem computedPracticalWindowStep_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (W : List (PairObservation (EuclideanSpace ℝ (Fin n))))
    (g : EuclideanSpace ℝ (Fin n)) (rho : ℝ) :
    computedPracticalWindowStep P (W.map (PairObservation.shift b)) g rho =
      computedPracticalWindowStep P W g rho := by
  classical
  unfold computedPracticalWindowStep
  dsimp only
  simp only [List.length_map]
  by_cases hz : W.length = 0
  · simp only [hz, ite_true]
  · simp only [hz, ite_false]
    rw [storedSteps_shift, storedImages_shift, selectedModel_shift]
    simp only [modelDirection_finCongr, modelTrialStep_finCongr, modelVirtualCorrection,
      (modelPhysicalData_finCongr (List.length_map ..) (storedSteps W) (storedImages W)
        (selectedModel P W) g).1]

/-- The actual fresh-secant model, including its cached scale, is invariant
under translation of all observation anchors. -/
theorem practicalModel_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    practicalModel P (S.shift b) = (practicalModel P S).shift b := by
  classical
  let W (S : State (EuclideanSpace ℝ (Fin n))) :=
    (rankWindow n S).drop (modelDeletion P (rankWindow n S))
  have hw : W (S.shift b) = (W S).map (PairObservation.shift b) := by
    simp only [W, rankWindow_shift, modelDeletion_shift, shift_drop]
  let rho (S : State (EuclideanSpace ℝ (Fin n))) :=
    freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs
  have hr : rho (S.shift b) = rho S := freshCurvature_shift b _ _
  change (⟨W (S.shift b), some (rho (S.shift b), rho (S.shift b)),
      computedPracticalWindowStep P (W (S.shift b)) (S.shift b).gradient (rho (S.shift b)),
      rho (S.shift b), (rankWindow n (S.shift b)).length,
      modelDeletion P (rankWindow n (S.shift b))⟩ : ModelResult _) =
    (⟨W S, some (rho S, rho S), computedPracticalWindowStep P (W S) S.gradient (rho S),
      rho S, (rankWindow n S).length, modelDeletion P (rankWindow n S)⟩ : ModelResult _).shift b
  rw [hw, hr, rankWindow_shift, modelDeletion_shift]
  simp only [computedPracticalWindowStep_shift, List.length_map, State.shift, ModelResult.shift]

/-- Literal raw execution transports every state, including rejected probes. -/
theorem rawPracticalRun_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (bounds : SpectralBounds) (k : ℕ) :
    rawPracticalRun P (fun x => f (x - b)) (fun x => G (x - b)) b bounds k =
      (rawPracticalRun P f G 0 bounds k).shift b := by
  unfold rawPracticalRun
  rw [algorithmInitialState_shift]
  exact rawRun_shift b P n (practicalModel P) (practicalModel_shift b P) f G _ k

/-- The computed new-direction scalar also commutes with translation. -/
theorem practicalTrialParameter_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    practicalTrialParameter P (S.shift b) = practicalTrialParameter P S := by
  classical
  unfold practicalTrialParameter
  dsimp only
  rw [practicalModel_shift]
  simp only [ModelResult.shift, List.length_map,
    show (S.shift b).gradient = S.gradient from rfl,
    storedSteps_shift, storedImages_shift, selectedModel_shift,
    modelDirection_finCongr, modelTrialLength_finCongr]

/-- Observation transport is valid for either accepted or rejected events. -/
theorem practical_rawObservationEvent_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (length : ℝ) (accept : Bool) (S : State (EuclideanSpace ℝ (Fin n))) :
    rawObservationEvent (practicalModel P) (fun x => f (x - b)) (fun x => G (x - b))
      length accept (S.shift b) =
      (rawObservationEvent (practicalModel P) f G length accept S).shift b := by
  classical
  unfold rawObservationEvent
  rw [practicalModel_shift]
  simp only [ModelResult.shift]
  rw [observedTrialPair_shift, appendPositive_shift]
  cases accept <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, State.shift, List.map_map,
      Function.comp_def, shift_transport]
  · rfl
  · have hp : S.point + b + length • (practicalModel P S).direction - b =
        S.point + length • (practicalModel P S).direction := by abel
    simp only [hp]
    congr 1
    abel

/-- The full accepted/rejected stored-event trajectory commutes with a
change of origin, independently of any outer search or acceptance policy. -/
theorem practical_rawObservationRun_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (length : ℕ → ℝ) (move : ℕ → Bool)
    (S : State (EuclideanSpace ℝ (Fin n))) (k : ℕ) :
    rawObservationRun (practicalModel P) (fun x => f (x - b)) (fun x => G (x - b))
      length move (S.shift b) k =
      (rawObservationRun (practicalModel P) f G length move S k).shift b := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rawObservationRun, ih, practical_rawObservationEvent_shift]

/-- The totalized raw outer recursion reaches the true quadratic minimizer
from an arbitrary initial point. Its actual computed trials, including
the trial after a rejected probe, obey the stated nonzero restriction;
this theorem does not infer Armijo search existence from a default index. -/
theorem rawPracticalRun_translated_quadratic_terminates {n : ℕ} (P : Parameters)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g₀ x₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hatoms : referenceAtomCount base hb g₀ = n) (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let f := fun x => quadraticObjective (cgOperator base) g₀ constant (x - x₀)
      let G := fun x => quadraticGradient (cgOperator base) g₀ (x - x₀)
      let S := rawPracticalRun P f G x₀ bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → practicalTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (practicalModel P) f G 1 false S
         probe.pairs.length < n → practicalTrialParameter P probe ≠ 0)) :
    let G := fun x => quadraticGradient (cgOperator base) g₀ (x - x₀)
    let S := rawPracticalRun P
      (fun x => quadraticObjective (cgOperator base) g₀ constant (x - x₀)) G x₀ bounds (n + 1)
    S.gradient = 0 ∧ G S.point = 0 ∧
      S.point = CG.displacement (cgOperator base) g₀ n + x₀ := by
  let f := quadraticObjective (cgOperator base) g₀ constant
  let G := quadraticGradient (cgOperator base) g₀
  have ht : ∀ i,
      let S := rawPracticalRun P f G 0 bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → practicalTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (practicalModel P) f G 1 false S
         probe.pairs.length < n → practicalTrialParameter P probe ≠ 0) := by
    intro i
    have hi := htrials i
    dsimp only at hi ⊢
    rw [rawPracticalRun_shift] at hi
    simp only [practical_rawObservationEvent_shift] at hi
    simp only [practicalTrialParameter_shift] at hi
    simp only [State.shift, List.length_map] at hi
    exact hi
  have hh := rawPracticalRun_quadratic_terminates P base hb g₀ constant bounds
    hinitial hmaximum hn hatoms hsigma ht
  let S := rawPracticalRun P f G 0 bounds (n + 1)
  have he : rawPracticalRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1) =
      S.shift x₀ := rawPracticalRun_shift x₀ P f G bounds (n + 1)
  change (rawPracticalRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).gradient = 0 ∧
    G ((rawPracticalRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).point - x₀) = 0 ∧
    (rawPracticalRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).point = _
  rw [he]
  change S.gradient = 0 ∧ G (S.point + x₀ - x₀) = 0 ∧ S.point + x₀ = _
  rw [add_sub_cancel_right]
  exact ⟨hh.1, hh.2.1, congrArg (· + x₀) hh.2.2⟩


end
end krylov.XR

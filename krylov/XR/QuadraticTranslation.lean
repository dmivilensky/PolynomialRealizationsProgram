import krylov.XR.ModelTranslation
import krylov.XR.QuadraticAlgorithm

/-!
Article: main_krylov, thm:XR, arbitrary starting point on a true quadratic.
Use: apply the actual quadratic termination theorem after a proved change
of origin. The real cached anchors, rejected probe, backtracking and
computed nonzero-trial condition are transported, rather than replaced by
a reference trajectory assumption. Source: affine translation and the
proved literal full-atom quadratic invariant.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
set_option maxHeartbeats 800000

theorem modelDirection_finCongr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a c : ℕ} (h : a = c) (s y : Fin c → E) (T : Matrix (Fin c) (Fin c) ℝ) (g : E) :
    modelDirection (s ∘ finCongr h) (y ∘ finCongr h)
      (T.submatrix (finCongr h) (finCongr h)) g = modelDirection s y T g := by
  subst c
  rfl

theorem modelTrialLength_finCongr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {a c : ℕ} (h : a = c) (s y : Fin c → E) (T : Matrix (Fin c) (Fin c) ℝ) (g : E)
    (curvature : ℝ) :
    modelTrialLength (s ∘ finCongr h) (y ∘ finCongr h)
      (T.submatrix (finCongr h) (finCongr h)) g curvature = modelTrialLength s y T g curvature := by
  subst c
  rfl

theorem algorithmTrialParameter_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    algorithmTrialParameter P (S.shift b) = algorithmTrialParameter P S := by
  classical
  unfold algorithmTrialParameter
  dsimp only
  rw [algorithmModel_shift]
  simp only [ModelResult.shift, List.length_map,
    show (S.shift b).initialStep = S.initialStep from rfl,
    show (S.shift b).gradient = S.gradient from rfl]
  simp only [storedSteps_shift, storedImages_shift, selectedModel_shift,
    modelDirection_finCongr, modelTrialLength_finCongr, observedTrialCurvature_shift]

/-- An actual observation event commutes with a change of origin, even
when this event is only the rejected first probe. -/
theorem rawObservationEvent_shift {n : ℕ} (b : EuclideanSpace ℝ (Fin n))
    (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (length : ℝ) (accept : Bool) (S : State (EuclideanSpace ℝ (Fin n))) :
    rawObservationEvent (algorithmModel P) (fun x => f (x - b)) (fun x => G (x - b))
      length accept (S.shift b) =
      (rawObservationEvent (algorithmModel P) f G length accept S).shift b := by
  classical
  unfold rawObservationEvent
  rw [algorithmModel_shift]
  simp only [ModelResult.shift]
  rw [observedTrialPair_shift, appendPositive_shift]
  cases accept <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, State.shift, List.map_map,
      Function.comp_def, shift_transport]
  · rfl
  · have hp : S.point + b + length • (algorithmModel P S).direction - b =
        S.point + length • (algorithmModel P S).direction := by abel
    simp only [hp]
    congr 1
    abel

/-- Literal full-memory XR solves a positive quadratic from an arbitrary
initial point. Both real trials (before and after a rejected probe) obey
only the original nonzero-scalar restriction. -/
theorem rawAlgorithmRun_translated_quadratic_terminates {n : ℕ} (P : Parameters)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g₀ x₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hinitial : P.initialCapacity = n) (hmaximum : P.maximumCapacity = n) (hn : 0 < n)
    (hatoms : referenceAtomCount base hb g₀ = n) (hsigma : P.armijo < 1 / 2)
    (htrials : ∀ i,
      let f := fun x => quadraticObjective (cgOperator base) g₀ constant (x - x₀)
      let G := fun x => quadraticGradient (cgOperator base) g₀ (x - x₀)
      let S := rawAlgorithmRun P f G x₀ bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) f G 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0)) :
    let G := fun x => quadraticGradient (cgOperator base) g₀ (x - x₀)
    let S := rawAlgorithmRun P
      (fun x => quadraticObjective (cgOperator base) g₀ constant (x - x₀)) G x₀ bounds (n + 1)
    S.gradient = 0 ∧ G S.point = 0 ∧
      S.point = CG.displacement (cgOperator base) g₀ n + x₀ := by
  let f := quadraticObjective (cgOperator base) g₀ constant
  let G := quadraticGradient (cgOperator base) g₀
  have ht : ∀ i,
      let S := rawAlgorithmRun P f G 0 bounds i
      S.gradient ≠ 0 →
        (S.pairs.length < n → algorithmTrialParameter P S ≠ 0) ∧
        (let probe := rawObservationEvent (algorithmModel P) f G 1 false S
         probe.pairs.length < n → algorithmTrialParameter P probe ≠ 0) := by
    intro i
    have hi := htrials i
    dsimp only at hi ⊢
    rw [rawAlgorithmRun_shift] at hi
    simp only [rawObservationEvent_shift] at hi
    simp only [algorithmTrialParameter_shift] at hi
    simp only [State.shift, List.length_map] at hi
    exact hi
  have hh := rawAlgorithmRun_quadratic_terminates P base hb g₀ constant bounds
    hinitial hmaximum hn hatoms hsigma ht
  let S := rawAlgorithmRun P f G 0 bounds (n + 1)
  have he : rawAlgorithmRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1) =
      S.shift x₀ := rawAlgorithmRun_shift x₀ P f G bounds (n + 1)
  change (rawAlgorithmRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).gradient = 0 ∧
    G ((rawAlgorithmRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).point - x₀) = 0 ∧
    (rawAlgorithmRun P (fun x => f (x - x₀)) (fun x => G (x - x₀)) x₀ bounds (n + 1)).point = _
  rw [he]
  change S.gradient = 0 ∧ G (S.point + x₀ - x₀) = 0 ∧ S.point + x₀ = _
  rw [add_sub_cancel_right]
  exact ⟨hh.1, hh.2.1, congrArg (· + x₀) hh.2.2⟩

end
end krylov.XR

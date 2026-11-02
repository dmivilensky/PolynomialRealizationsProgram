import krylov.XR.GlobalAlgorithm
import krylov.XR.ModelStep

/-!
Article: Section 7 trial policies; Theorem 7.1 [thm:XR] and
Proposition 7.5 [prop:practical-trial].

The recent positive physical secant supplies the trial curvature. The actual
one-probe executor gives global stationarity through model-independent
Armijo globalization. PracticalGrowthInitialRates derives the conditional
local transition and rates with the article's independence and trial-adequacy
hypotheses. Source: the secant quotient and safeguarded model of Section 7.
-/

namespace krylov.XR
noncomputable section
open Filter krylov.Methods
open scoped InnerProductSpace NNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Curvature of an actual observation in its physical step metric. -/
def secantCurvature (a : PairObservation E) : ℝ :=
  inner ℝ a.step a.image / ‖a.step‖ ^ 2

/-- A positive observed pairing supplies a strictly positive trial scalar. -/
theorem secantCurvature_pos (a : PairObservation E) (ha : positivePair a) :
    0 < secantCurvature a := by
  have hs : a.step ≠ 0 := by
    intro hz
    simp [positivePair, hz] at ha
  exact div_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hs))

/-- Update from the newest actual positive pair; retain the scale otherwise.
The value is read before rank/refutation deletions, which cannot erase it. -/
def freshCurvature (previous : ℝ) (W : List (PairObservation E)) : ℝ := by
  classical
  exact match W.getLast? with
    | none => previous
    | some a => if positivePair a then secantCurvature a else previous

/-- No positive-history assumption is hidden in the scale update. -/
theorem freshCurvature_pos (previous : ℝ) (hp : 0 < previous)
    (W : List (PairObservation E)) : 0 < freshCurvature previous W := by
  classical
  unfold freshCurvature
  split
  · exact hp
  · split
    · exact secantCurvature_pos _ (by assumption)
    · exact hp

/-- The concrete practical model uses the unchanged selection and F gate.
For compatibility with the existing executor, its optional `bounds` slot
carries `(rho,rho)`, a cached scalar, and never historical spectral extrema.
This interpretation applies only to `practicalModel`/`practicalRun` states. -/
def practicalModel {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    ModelResult (EuclideanSpace ℝ (Fin n)) := by
  classical
  let rho := freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs
  let W₀ := rankWindow n S
  let o := modelDeletion P W₀
  let W := W₀.drop o
  let u := if W.length = 0 then -(rho⁻¹) • S.gradient else
    let s := storedSteps W
    let y := storedImages W
    let T := selectedModel P W
    if W.length = n then modelVirtualCorrection s T S.gradient else
      modelTrialStep s y T S.gradient (rho * ‖modelDirection s y T S.gradient‖ ^ 2)
  exact ⟨W, some (rho, rho), u, rho, W₀.length, o⟩

/-- Trial policy changes neither the observed window nor its bookkeeping. -/
theorem practicalModel_window {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    (practicalModel P S).pairs = (algorithmModel P S).pairs ∧
    (practicalModel P S).pairsBeforeTest = (algorithmModel P S).pairsBeforeTest ∧
    (practicalModel P S).deletedByTest = (algorithmModel P S).deletedByTest := by
  exact ⟨rfl, rfl, rfl⟩

/-- Full memory has exactly the old SS1/SS1-F correction, independent of rho. -/
theorem practicalModel_full {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hn : 0 < n) (hw : (practicalModel P S).pairs.length = n) :
    (practicalModel P S).direction =
      modelVirtualCorrection (storedSteps (practicalModel P S).pairs)
        (selectedModel P (practicalModel P S).pairs) S.gradient := by
  classical
  unfold practicalModel at hw ⊢
  dsimp only at hw ⊢
  rw [ite_eq_right (by omega), ite_eq_left hw]

/-- Practical execution uses the same observed one-probe/Armijo recursion.
Its fresh scale starts at the reciprocal of the initial infinity-norm step. -/
def practicalRun {n : ℕ} (P : Parameters) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  run P n (practicalModel P) f G (algorithmInitialState P f G x₀ none)

/-- Global stationarity requires no spectral estimate or local trial-adequacy
assumption. This is an instantiation of the established executor theorem. -/
theorem practicalRun_global {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hb : ∃ b, ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k => ‖G (practicalRun P f G x₀ k).point‖ ^ 2) ∧
      Tendsto (fun k => ‖G (practicalRun P f G x₀ k).point‖) atTop (𝓝 0) ∧
      ∀ (z : EuclideanSpace ℝ (Fin n)) (indices : ℕ → ℕ), Tendsto indices atTop atTop →
        Tendsto ((fun k => (practicalRun P f G x₀ k).point) ∘ indices) atTop (𝓝 z) →
          G z = 0 := by
  have hs : Summable (fun k => ‖G (practicalRun P f G x₀ k).point‖ ^ 2) := by
    by_cases hg : G x₀ = 0
    · have hr k : practicalRun P f G x₀ k = algorithmInitialState P f G x₀ none :=
        run_stationary P n (practicalModel P) f G _ hg k
      simp only [hr, algorithmInitialState, initialState, hg, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0)]
      exact summable_zero
    · have hc := algorithmInitialState_constants P hP f G x₀ none hg
      rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
      exact run_gradient_square_summable P n (practicalModel P) f G hF L hL hG
        hsig (hsig₁.trans (by norm_num)) _ hc.1 hc.2 rfl rfl hb
  refine ⟨hs, gradient_norm_tendsto_zero _ G hs, ?_⟩
  intro z indices hi hx
  exact stationary_of_limit _ G hG.continuous hs z indices hi hx

end
end krylov.XR

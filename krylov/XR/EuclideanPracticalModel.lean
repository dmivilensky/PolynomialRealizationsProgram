import krylov.XR.Practical
import krylov.XR.EuclideanModelBasic

/-!
# Practical XR-F with the Euclidean split

Article: Corollary 7.4 [cor:xrF] of krylov.tex.
The fresh positive secant scale is used in the actual missing direction;
the selected value diagonal is computed from the Euclidean split at the
current anchor. Window selection and the generic observed executor are shared.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator

/-- The literal practical model with the Euclidean value split. -/
def euclideanPracticalModel {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) : ModelResult (EuclideanSpace ℝ (Fin n)) := by
  classical
  let rho := freshCurvature (fallbackCurvature S.bounds S.initialStep) S.pairs
  let W₀ := rankWindow n S
  let o := modelDeletion P W₀
  let W := W₀.drop o
  let u := if W.length = 0 then -(rho⁻¹) • S.gradient else
    let s := storedSteps W
    let y := storedImages W
    let T := selectedEuclideanModel P S.point W
    if W.length = n then modelVirtualCorrection s T S.gradient else
      modelTrialStep s y T S.gradient (rho * ‖modelDirection s y T S.gradient‖ ^ 2)
  exact ⟨W, some (rho, rho), u, rho, W₀.length, o⟩

/-- Actual Euclidean-split practical execution uses the same one-probe Armijo recursion. -/
def euclideanPracticalRun {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → State (EuclideanSpace ℝ (Fin n)) :=
  run P n (euclideanPracticalModel P) f G (algorithmInitialState P f G x₀ none)

/-- The full-window practical correction contains no missing-direction scale. -/
theorem euclideanPracticalModel_full {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (hn : 0 < n)
    (hw : (euclideanPracticalModel P S).pairs.length = n) :
    (euclideanPracticalModel P S).direction =
      modelVirtualCorrection (storedSteps (euclideanPracticalModel P S).pairs)
        (selectedEuclideanModel P S.point (euclideanPracticalModel P S).pairs) S.gradient := by
  classical
  unfold euclideanPracticalModel at hw ⊢
  dsimp only at hw ⊢
  rw [ite_eq_right (by omega), ite_eq_left hw]

/-- Global stationarity requires no spectral estimate or local trial-adequacy
assumption. This is an instantiation of the established executor theorem. -/
theorem euclideanPracticalRun_global {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x)
    (L : ℝ≥0) (hL : 0 < (L : ℝ)) (hG : LipschitzWith L G)
    (hb : ∃ b, ∀ x, b ≤ f x) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Summable (fun k => ‖G (euclideanPracticalRun P f G x₀ k).point‖ ^ 2) ∧
      Tendsto (fun k => ‖G (euclideanPracticalRun P f G x₀ k).point‖) atTop (𝓝 0) ∧
      ∀ (z : EuclideanSpace ℝ (Fin n)) (indices : ℕ → ℕ), Tendsto indices atTop atTop →
        Tendsto ((fun k => (euclideanPracticalRun P f G x₀ k).point) ∘ indices) atTop (𝓝 z) →
          G z = 0 := by
  have hs : Summable (fun k => ‖G (euclideanPracticalRun P f G x₀ k).point‖ ^ 2) := by
    by_cases hg : G x₀ = 0
    · have hr k : euclideanPracticalRun P f G x₀ k = algorithmInitialState P f G x₀ none :=
        run_stationary P n (euclideanPracticalModel P) f G _ hg k
      simp only [hr, algorithmInitialState, initialState, hg, norm_zero,
        zero_pow (by norm_num : 2 ≠ 0)]
      exact summable_zero
    · have hc := algorithmInitialState_constants P hP f G x₀ none hg
      rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
      exact run_gradient_square_summable P n (euclideanPracticalModel P) f G hF L hL hG
        hsig (hsig₁.trans (by norm_num)) _ hc.1 hc.2 rfl rfl hb
  refine ⟨hs, gradient_norm_tendsto_zero _ G hs, ?_⟩
  intro z indices hi hx
  exact stationary_of_limit _ G hG.continuous hs z indices hi hx

end
end krylov.XR

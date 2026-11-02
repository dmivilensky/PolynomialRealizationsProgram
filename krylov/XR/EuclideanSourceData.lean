import krylov.XR.EuclideanSourceTerms
import krylov.XR.EuclideanWindowBounds

/-!
Article: main_krylov, cor:xrF, primitive actual corrected-model source data.
Use: prove arbitrarily small normalized error for the actual computed
value model and eventual exact retention of every scalar value term.
All observations are those of the literal safeguarded algorithm, with
either setting of F, and their localization is derived from original G1.
Source: genuine memory forgetting, Lipschitz-Hessian defects and actual gates.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Primitive G1 source yields both the actual scalar gates and complete
normalized corrected-model approximation on every late real ModelStep. -/
theorem euclideanAlgorithmRun_eventually_corrected_data (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K, ∀ k, K ≤ k →
      let W := (euclideanAlgorithmModel P (euclideanAlgorithmRun P f G x₀ bounds k)).pairs
      (∀ i : Fin W.length, ‖storedImages W i - H center (storedSteps W i)‖ ≤
        epsilon * ‖storedSteps W i‖) ∧
      (∀ i : Fin W.length, |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
      ‖rescaleModel (euclideanStoredValueModel (euclideanAlgorithmRun P f G x₀ bounds k).point W) (fun i => ‖storedSteps W i‖⁻¹) -
        localReferenceGram (H center) (krylov.Convergence.unitWindow (storedSteps W))‖ ≤
          (W.length : ℝ) * epsilon := by
  let e : ℝ≥0 := ⟨epsilon / 2, by positivity⟩
  have he : 0 < (e : ℝ) := by change 0 < epsilon / 2; positivity
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne e he
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_value_terms P hP f G H x₀ center bounds
    hF hG hH radius hradius L hLip mu hmu hpositive hconv hne (epsilon / 2) (by positivity)
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  let W := (euclideanAlgorithmModel P S).pairs
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (euclideanAlgorithmRun_pairs_positive P f G x₀ bounds k _
      (euclideanAlgorithmModel_pair_mem P S _ (List.get_mem _ i)))
  have hy (i : Fin W.length) : ‖storedImages W i - H center (storedSteps W i)‖ ≤
      epsilon / 2 * ‖storedSteps W i‖ :=
    hK₁ k (by omega) _ (euclideanAlgorithmModel_pair_mem P S _ (List.get_mem _ i))
  have hv (i : Fin W.length) := hK₂ k (by omega) _ (euclideanAlgorithmModel_pair_mem P S _ (List.get_mem W i))
  have hscalar (i : Fin W.length) :
      |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ epsilon / 2 * ‖storedSteps W i‖ ^ 2 := by
    exact (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hgate (i : Fin W.length) :
      |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2 := by
    have hb := (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    have hc := (hv i).1
    change (mu / 2) * ‖storedSteps W i‖ ^ 2 ≤ storedPairing W i i at hc
    change |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ (mu / 4) * ‖storedSteps W i‖ ^ 2 at hb
    nlinarith
  have hmodel := euclideanStoredValueModel_normalized_error S.point (H center) hsym W hs (epsilon / 2) (epsilon / 2)
    (by positivity) (by positivity) hy (fun i => (euclideanStoredValueTerm_abs_le S.point W i).trans (hscalar i))
  refine ⟨?_, hgate, ?_⟩
  · intro i
    exact (hy i).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · simpa only [show epsilon / 2 + epsilon / 2 = epsilon by ring] using hmodel

end
end krylov.XR

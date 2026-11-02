import krylov.XR.EuclideanSourceData
import krylov.XR.EuclideanGate
import krylov.XR.EuclideanRetention

/-!
Article: main_krylov, cor:xrF, actual eventual corrected-model selection.
Use: derive both real value gates from original G1--G2. The function
source, pre-cleanup independence and genuine retained endpoint data imply
the exact complex test; eventual corrected-model selection is a conclusion.
Source: true normalized model approximation and the proved relative gate.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- On every sufficiently late actual first ModelStep with F enabled,
the true scalar terms and the corrected Hermitian gate all pass. -/
theorem euclideanAlgorithmRun_eventually_corrected_gates (P : Parameters) (hP : P.Valid n)
    (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanAlgorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let W := (euclideanAlgorithmModel P (euclideanAlgorithmRun P f G x₀ bounds k)).pairs
      (∀ i : Fin W.length, |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        euclideanCorrectedWindowPasses P.windowThreshold (euclideanAlgorithmRun P f G x₀ bounds k).point W ∧ selectedEuclideanModel P (euclideanAlgorithmRun P f G x₀ bounds k).point W = euclideanStoredValueModel (euclideanAlgorithmRun P f G x₀ bounds k).point W := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  have hsmall : (n : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1))).mp
      (min_le_left (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (8 * ((n : ℝ) + 1)) ≤ _ at h
    nlinarith
  have hgate : 2 * (n : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp
      (min_le_right (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (4 * ((n : ℝ) + 1)) ≤ _ at h
    apply (div_lt_iff₀ hcoerc).2
    nlinarith [mul_pos htheta hcoerc]
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_corrected_data P hP f G H x₀ center bounds hF hG hH
    radius hradius L hLip mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_retains_window P hP f G H x₀ center bounds hF hG hH
    mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₀ (max K₁ K₂), ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  let W := (euclideanAlgorithmModel P S).pairs
  have hdata := hK₁ k (by omega)
  have hret : W = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : W.length ≤ n := (euclideanAlgorithmModel_length_le P S).trans (min_le_right _ _)
  have hlenR : (W.length : ℝ) ≤ n := by exact_mod_cast hlen
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (euclideanAlgorithmRun_pairs_positive P f G x₀ bounds k _
      (euclideanAlgorithmModel_pair_mem P S _ (List.get_mem _ i)))
  have hgain : ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2 := by
    rw [hret]
    exact hgain k (by omega)
  have hpass := euclideanCorrectedWindowPasses_of_errors P.windowThreshold htheta S.point (H center) hsym W hs
    mu sigma epsilon hmu hsigma hepsilon.le hpositive hgain hdata.1 hdata.2.2
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)
  exact ⟨hdata.2.1, hpass, ite_eq_left ⟨hon, hpass⟩⟩

end
end krylov.XR

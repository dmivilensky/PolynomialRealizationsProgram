import krylov.XR.EuclideanLocalMemory
import krylov.XR.LocalModelActivation

/-!
Article: main_krylov, thm:grow, eventual genuine window retention.
Use: combine original G1 data and G2 on incoming windows to derive that
the actual rank and Hermitian tests eventually delete no observation.
Actual relative secant errors, locality and limiting Hessian symmetry are
proved from the function; no eventual successful-test field is assumed.
Source: genuine memory forgetting, Schwarz symmetry and local raw bounds.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- Original local source and pre-cleanup G2 force actual eventual rank
and refutation-test retention in the literal data-only algorithm. -/
theorem euclideanAlgorithmRun_eventually_retains_window (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
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
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      rankDeletion (incomingWindow S) = 0 ∧
        (euclideanAlgorithmModel P S).pairs = incomingWindow S ∧
        (euclideanAlgorithmModel P S).pairsBeforeTest = (incomingWindow S).length ∧
        (euclideanAlgorithmModel P S).deletedByTest = 0 := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  let e : ℝ≥0 := ⟨epsilon, hepsilon.le⟩
  have hsmall : (n : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 := by
    have h := min_le_left (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
      (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
    change epsilon ≤ _ at h
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1))).mp h
    nlinarith [hepsilon]
  have hgate : 2 * (n : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold := by
    have h := min_le_right (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
      (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
    change epsilon ≤ _ at h
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp h
    apply (div_lt_iff₀ hcoerc).2
    nlinarith [mul_pos htheta hcoerc, hepsilon]
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_secant_errors P hP f G H x₀ center bounds hF hG hH
    mu hmu hpositive hconv hne e hepsilon
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  have hlen : (incomingWindow S).length ≤ n := by
    simp only [incomingWindow, retainNewest_length]
    omega
  have hlenR : ((incomingWindow S).length : ℝ) ≤ n := by exact_mod_cast hlen
  have hy i : ‖storedImages (incomingWindow S) i - H center (storedSteps (incomingWindow S) i)‖ ≤
      epsilon * ‖storedSteps (incomingWindow S) i‖ := by
    exact hK₁ k (by omega) _ (List.mem_of_mem_drop (List.get_mem _ i))
  change rankDeletion (incomingWindow S) = 0 ∧
    (algorithmModel P S).pairs = incomingWindow S ∧
    (algorithmModel P S).pairsBeforeTest = (incomingWindow S).length ∧
    (algorithmModel P S).deletedByTest = 0
  exact algorithmModel_local_retention P htheta S (euclideanAlgorithmRun_pairs_positive P f G x₀ bounds k)
    (H center) hsym mu sigma epsilon hmu hsigma hepsilon.le hpositive (hgain k (by omega)) hy
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)

end
end krylov.XR

import krylov.XR.EuclideanFullEntry

/-!
Article: main_krylov, thm:grow and cor:xrF, full initial memory without G3.
Use: full memory is derived through actual safeguarded/rejected-probe
execution before imposing any partial-trial adequacy; the latter is then
vacuous. Both settings of the value flag use the true selected-model bounds.
Source: original G1--G2, G4, genuine value diagonals and finite memory filling.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The original full-initial-memory source admits a genuine selected-model
local-source certificate with no partial-trial adequacy premise. This
constructor feeds the actual SS1-F execution and rate dictionaries. -/
theorem euclideanGrowthSource_exists_of_initial_full (P : Parameters) (hP : P.Valid n)
    (hfull : P.initialCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper ell trialUpper eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (heta : 0 < eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanAlgorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (euclideanAlgorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ bounds).descentConstant <
      dimensionDescentConstant n mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant n mu sigma upper ell <
      (algorithmInitialState P f G x₀ bounds).normConstant) :
    Nonempty (EuclideanGrowthSource P f G H x₀ center bounds) := by
  obtain ⟨K, hK⟩ := euclideanAlgorithmRun_eventually_full_of_initial_full P hP hfull f G H x₀ center bounds
    hF hG hHC.self_of_nhds mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
  let D : EuclideanGrowthSource P f G H x₀ center bounds :=
    { mu := mu, sigma := sigma, upper := upper, ell := ell, trialUpper := trialUpper, eta := eta
      mu_pos := hmu, sigma_pos := hsigma, upper_pos := hupper, ell_pos := hell
      trialUpper_pos := htrialUpper, eta_pos := heta, f_deriv := hF, g_deriv := hG, h_cont := hHC
      sourceRadius := radius, sourceRadius_pos := hradius, hessianLipschitz := L, h_lip := hLip
      coercive := hpositive, h_norm := hHnorm, converges := hconv, distinct := hne
      gainStart := K₀, gain := hgain, trialStart := K
      trial := by
        intro k hk
        dsimp only
        intro _ hp
        have hh := hK k hk
        omega
      safeguard_descent := hG₄₁, safeguard_norm := hG₄₂ }
  exact ⟨D⟩

end
end krylov.XR

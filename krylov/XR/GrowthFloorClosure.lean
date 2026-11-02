import krylov.XR.GrowthFloorSource
import krylov.XR.CorrectedGrowth

/-!
Article: main_krylov, thm:XR, thm:grow and cor:xrF, source-only floor closure.
Use: feed source-derived actual G3 into the original growth theorem. The
numeric G4 constants are exposed after the real uniform running upper
bound has been derived. There is no prescribed acceptance, memory phase
or curvature-accuracy field. Source: genuine G1--G2, the literal running
upper margin, and the proved source floor theorem.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Primitive local source and a genuine strict running upper margin
construct the original selected growth source without a G3 hypothesis.
The remaining implications are exactly the original strict numeric G4. -/
theorem selectedGrowthSource_exists_of_strict_running_upper (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef) (hcenter : H center = cgOperator base)
    (b : ℝ) (hab : mu ≤ b) (hb : 0 < b) (hnorm : ‖cgOperator base‖ ≤ b)
    (hsigma₁ : sigma ≤ 1)
    (hHlo : (base-mu • 1).PosSemidef) (hHhi : (b • 1-base).PosSemidef)
    (Kstrict : ℕ) (strictBounds : ℝ × ℝ)
    (hstrictBounds : (algorithmRun P f G x₀ bounds Kstrict).bounds = some strictBounds)
    (hstrict : b < strictBounds.2)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius)) :
    ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant n mu sigma b trialUpper) →
      (dimensionNormConstant n mu sigma b
        (mu/(2*(2*(1-P.armijo)-P.adequacyMargin))) <
          (algorithmInitialState P f G x₀ bounds).normConstant) →
      Nonempty (SelectedGrowthSource P f G H x₀ center bounds) := by
  obtain ⟨trialUpper, htrialUpper, K, hK⟩ := algorithmRun_eventually_floored_adequate P hP f G H x₀ center bounds
    hF hG hHC.self_of_nhds mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
    base hbase hcenter b hab hb hnorm hsigma₁ hHlo hHhi Kstrict strictBounds hstrictBounds hstrict
  refine ⟨trialUpper, htrialUpper, ?_⟩
  intro hG₄₁ hG₄₂
  have hell : 0 < mu/(2*(2*(1-P.armijo)-P.adequacyMargin)) := by
    have hh := hP.2.2.2.2.2.2.2.2.2.2.2
    have hA : 0 < 2*(1-P.armijo)-P.adequacyMargin := by linarith
    exact div_pos hmu (mul_pos (by norm_num) hA)
  have heta : 0 < P.adequacyMargin/2 := half_pos hP.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨{
    mu := mu, sigma := sigma, upper := b
    ell := mu/(2*(2*(1-P.armijo)-P.adequacyMargin))
    trialUpper := trialUpper, eta := P.adequacyMargin/2
    mu_pos := hmu, sigma_pos := hsigma, upper_pos := hb, ell_pos := hell
    trialUpper_pos := htrialUpper, eta_pos := heta
    f_deriv := hF, g_deriv := hG, h_cont := hHC
    sourceRadius := radius, sourceRadius_pos := hradius
    hessianLipschitz := L, h_lip := hLip
    coercive := hpositive
    h_norm := by rw [hcenter]; exact hnorm
    converges := hconv, distinct := hne, gainStart := K₀, gain := hgain
    trialStart := K
    trial := by
      intro k hk
      dsimp only
      intro _ _ hd
      exact hK k hk hd
    safeguard_descent := hG₄₁, safeguard_norm := hG₄₂ }⟩

end
end krylov.XR

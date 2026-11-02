import krylov.XR.GrowthFloorClosure
import krylov.XR.LocalSpectralBand

/-!
Article: main_krylov, thm:XR, original strict-upper source assumptions.
Use: remove auxiliary matrix spectral-band and sigma≤1 assumptions from
the actual floor closure. Their certificates are proved from the original
physical positive Hessian, original incoming G2 and a real strict running
upper margin. Source: physical operator/matrix correspondence and harmless
weakening of the original positive independence/coercivity constants.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original primitive G1--G2 and an actual strict running upper margin
supply a genuine growth source for either value flag. All auxiliary band,
normalization, G3 and model-domain hypotheses are discharged internally. -/
theorem selectedGrowthSource_from_original_floor (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
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
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (Kstrict : ℕ) (strictBounds : ℝ × ℝ)
    (hstrictBounds : (algorithmRun P f G x₀ bounds Kstrict).bounds = some strictBounds)
    (hstrict : ‖H center‖ < strictBounds.2) :
    let b := (‖H center‖ + strictBounds.2)/2
    let a := min mu b
    let gain := min sigma 1
    ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant n a gain b trialUpper) →
      (dimensionNormConstant n a gain b
        (a/(2*(2*(1-P.armijo)-P.adequacyMargin))) <
          (algorithmInitialState P f G x₀ bounds).normConstant) →
      Nonempty (SelectedGrowthSource P f G H x₀ center bounds) := by
  let b := (‖H center‖+strictBounds.2)/2
  let a := min mu b
  let gain := min sigma 1
  have hb : 0 < b := by dsimp only [b]; nlinarith [norm_nonneg (H center)]
  have ha : 0 < a := lt_min hmu hb
  have hab : a ≤ b := min_le_right _ _
  have hmargin : b < strictBounds.2 := by dsimp only [b]; linarith
  have hnorm : ‖cgOperator base‖ ≤ b := by rw [←hcenter]; dsimp only [b]; linarith
  have hpos : ∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ inner ℝ v (H center v) := by
    intro v
    exact (mul_le_mul_of_nonneg_right (min_le_left mu b) (sq_nonneg ‖v‖)).trans (hpositive v)
  have hposBase : ∀ v : EuclideanSpace ℝ (Fin n), a*‖v‖^2 ≤ inner ℝ v (cgOperator base v) := by
    rw [←hcenter]
    exact hpos
  have hband := operator_bounds_spectral_band base hbase a b hposBase hnorm
  have hgainPos : 0 < gain := lt_min hsigma (by norm_num)
  have hgainOne : gain ≤ 1 := min_le_right _ _
  have hgainSq : gain^2 ≤ sigma^2 := by have := min_le_left sigma 1; nlinarith [hgainPos]
  have hgain' : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, gain^2*‖WithLp.toLp 2 w‖^2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖^2 := by
    intro k hk
    dsimp only
    intro w
    exact (mul_le_mul_of_nonneg_right hgainSq (sq_nonneg _)).trans (hgain k hk w)
  have hprobeGain' : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, gain^2*‖WithLp.toLp 2 w‖^2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖^2 := by
    intro k hk
    dsimp only
    intro hreject w
    exact (mul_le_mul_of_nonneg_right hgainSq (sq_nonneg _)).trans (hprobeGain k hk hreject w)
  have hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hradius)] with z hz
    exact hLip.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)
  exact selectedGrowthSource_exists_of_strict_running_upper P hP f G H x₀ center bounds
    hF hG hHC a gain ha hgainPos hpos hconv hne K₀ hgain' hprobeGain'
    base hbase hcenter b hab hb hnorm hgainOne hband.1 hband.2 Kstrict strictBounds
    hstrictBounds hmargin radius hradius L hLip

end
end krylov.XR

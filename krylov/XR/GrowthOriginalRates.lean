import krylov.XR.GrowthOriginalTransition
import krylov.Convergence.WindowSelectedOrdinary
import krylov.Convergence.WindowNativeValueRate

/-!
Article: main_krylov, thm:XR and cor:xrF, native original-floor R-orders.
Use: combine the entirely source-derived G3-free floor transition with the
actual chronological SS1/SS1-F execution dictionaries and physical rates.
The true scalar accepted trajectory is the output; no rate, recurrence,
successful gate, full-window phase or trial-accuracy premise is supplied.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear krylov.Convergence
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The original strict-upper XR source has its literal physical ordinary
R-order, with source-derived G3 and the remaining numeric G4 exposed. -/
theorem original_floor_XR_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
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
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef) (hcenter : H center = cgOperator base)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (hupperMargin : ∃ k, ‖H center‖ <
      boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds)
    (hoff : P.valuesEnabled = false) (hmax : P.maximumCapacity = n+1) :
    ∃ a > 0, ∃ gain > 0, ∃ b > 0, ∃ ell > 0, ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant (n+1) a gain b trialUpper) →
      (dimensionNormConstant (n+1) a gain b ell <
        (algorithmInitialState P f G x₀ bounds).normConstant) →
      HasROrder (fun k => ‖(metricCoordinates base hbase)
        ((algorithmRun P f G x₀ bounds k).point-center)‖) (oneGradientRoot (n+2)) := by
  obtain ⟨a, ha, gain, hgain, b, hb, ell, hell, trialUpper, htrialUpper, hsource⟩ :=
    algorithmRun_original_floor_transition P hP f G H x₀ center bounds
    hF hG mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
    base hbase hcenter radius hradius L hLip hupperMargin
  refine ⟨a, ha, gain, hgain, b, hb, ell, hell, trialUpper, htrialUpper, ?_⟩
  intro hG₄₁ hG₄₂
  obtain ⟨⟨D⟩, _⟩ := hsource hG₄₁ hG₄₂
  obtain ⟨rG, hrG, hderiv⟩ := Metric.eventually_nhds_iff.mp hG
  let r := min radius rG
  have hr : 0 < r := lt_min hradius hrG
  have hsub : ball center r ⊆ ball center radius := ball_subset_ball (min_le_left _ _)
  have hGS : ∀ z ∈ ball center r, HasFDerivAt G (H z) z := by
    intro z hz
    exact hderiv ((ball_subset_ball (min_le_right radius rG)) hz)
  exact selected_source_full_XR_physical_rorder P f G H x₀ center bounds D hP hoff hmax
    base hbase hcenter (ball center r) (convex_ball center r) (mem_ball_self hr)
    (isOpen_ball.mem_nhds (mem_ball_self hr)) (hLip.mono hsub) hGS

/-- The actual value-enabled algorithm has its printed improved physical
R-order from genuine third derivatives and exact endpoint values. -/
theorem original_floor_XRF_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
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
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef) (hcenter : H center = cgOperator base)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (hupperMargin : ∃ k, ‖H center‖ <
      boundsUpper (algorithmModel P (algorithmRun P f G x₀ bounds k)).bounds)
    (hon : P.valuesEnabled = true) (hmax : P.maximumCapacity = n+1)
    (hfBall : ∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hGBall : ∀ z ∈ ball center radius, HasFDerivAt G (H z) z)
    (T₃ : EuclideanSpace ℝ (Fin (n+1)) → krylov.Functions.SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    {L₃ : ℝ≥0}
    (hT : ∀ z ∈ centeredMetricDomain (metricCoordinates base hbase) center (ball center radius),
      HasFDerivAt (gradientHessian (centeredMetricHessian (metricCoordinates base hbase) center H)) (T₃ z).form z)
    (hTLip : ∀ z ∈ centeredMetricDomain (metricCoordinates base hbase) center (ball center radius),
      ∀ w ∈ centeredMetricDomain (metricCoordinates base hbase) center (ball center radius), ∀ h, ‖h‖ = 1 →
      |(T₃ z).form h h h - (T₃ w).form h h h| ≤ (L₃ : ℝ)*‖z-w‖) :
    ∃ a > 0, ∃ gain > 0, ∃ b > 0, ∃ ell > 0, ∃ trialUpper > 0,
      ((algorithmInitialState P f G x₀ bounds).descentConstant <
        dimensionDescentConstant (n+1) a gain b trialUpper) →
      (dimensionNormConstant (n+1) a gain b ell <
        (algorithmInitialState P f G x₀ bounds).normConstant) →
      HasROrder (fun k => ‖(metricCoordinates base hbase)
        ((algorithmRun P f G x₀ bounds k).point-center)‖) (oneGradientRoot (n+1)) := by
  obtain ⟨a, ha, gain, hgain, b, hb, ell, hell, trialUpper, htrialUpper, hsource⟩ :=
    algorithmRun_original_floor_transition P hP f G H x₀ center bounds
    hF hG mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
    base hbase hcenter radius hradius L hLip hupperMargin
  refine ⟨a, ha, gain, hgain, b, hb, ell, hell, trialUpper, htrialUpper, ?_⟩
  intro hG₄₁ hG₄₂
  obtain ⟨⟨D⟩, _⟩ := hsource hG₄₁ hG₄₂
  exact selected_source_full_XRF_physical_rorder P f G H x₀ center bounds D hP hon hmax
    base hbase hcenter (ball center radius) (convex_ball center radius) (mem_ball_self hradius)
    (isOpen_ball.mem_nhds (mem_ball_self hradius)) hLip hfBall hGBall T₃ hT hTLip

end
end krylov.XR

import krylov.XR.EuclideanFullSource
import krylov.Convergence.EuclideanWindowRate

/-!
Article: main_krylov, cor:xrF, the initially full Euclidean-split executor.
Use: retain the original G3-free full-initial-memory case in the actual
physical XR-F rate. The genuine finite-memory source constructor makes
partial-window adequacy vacuous; no phase or rate is supplied as a premise.
Source: actual observed Euclidean correction and proved SS1-F chronology.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Convergence krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- XR-F with initially full memory has its improved physical order from
actual C3,1 data, genuine endpoint values and the original source assumptions. -/
theorem euclidean_initial_full_XRF_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
    (hfull : P.initialCapacity = (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1))) (bounds : SpectralBounds)
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
      dimensionDescentConstant (n+1) mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant (n+1) mu sigma upper ell <
      (algorithmInitialState P f G x₀ bounds).normConstant)
    (hon : P.valuesEnabled = true)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center = krylov.Reference.cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center ∈ S) (hn : S ∈ 𝓝 center) {L₁ : ℝ≥0}
    (hHL : LipschitzOnWith L₁ H S)
    (hGS : ∀ z ∈ S, HasFDerivAt G (H z) z)
    (hfS : ∀ z ∈ S, HasFDerivAt f (innerSL ℝ (G z)) z)
    (T₃ : EuclideanSpace ℝ (Fin (n+1)) → krylov.Functions.SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    {L₃ : ℝ≥0}
    (hT : ∀ z ∈ centeredMetricDomain (metricCoordinates base hb) center S,
      HasFDerivAt (gradientHessian (centeredMetricHessian (metricCoordinates base hb) center H)) (T₃ z).form z)
    (hTLip : ∀ z ∈ centeredMetricDomain (metricCoordinates base hb) center S,
      ∀ w ∈ centeredMetricDomain (metricCoordinates base hb) center S, ∀ h, ‖h‖ = 1 →
      |(T₃ z).form h h h - (T₃ w).form h h h| ≤ (L₃ : ℝ) * ‖z-w‖) :
    HasROrder (fun k => ‖(metricCoordinates base hb)
      ((euclideanAlgorithmRun P f G x₀ bounds k).point - center)‖) (oneGradientRoot (n+1)) := by
  obtain ⟨D⟩ := euclideanGrowthSource_exists_of_initial_full P hP hfull f G H x₀ center bounds
    hF hG hHC radius hradius L hLip mu sigma upper ell trialUpper eta
    hmu hsigma hupper hell htrialUpper heta hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
  have hmax : P.maximumCapacity = n+1 := by
    have := hP.2.1
    have := hP.2.2.1
    omega
  exact euclidean_source_full_XRF_physical_rorder P f G H x₀ center bounds D hP hon hmax
    base hb hbase S hS hc hn hHL hfS hGS T₃ hT hTLip

end
end krylov.XR

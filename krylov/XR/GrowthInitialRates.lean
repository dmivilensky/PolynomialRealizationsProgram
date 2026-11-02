import krylov.XR.CorrectedFullSource
import krylov.Convergence.WindowSelectedOrdinary
import krylov.Convergence.WindowNativeValueRate

/-!
Article: main_krylov, thm:XR, thm:grow and cor:xrF, initially full memory.
Use: conclude the actual physical R-orders directly from primitive local
source hypotheses and incoming-window G2, without any partial-trial G3
hypothesis. Actual full-window activation and scalar sequence dictionaries
are derived by the imported source theorems. Source: the original m0=n
case, true Hessian root normalization, and genuine SS1/SS1-F R-orders.
-/

namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Nonlinear krylov.Convergence
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Ordinary literal XR with initially full memory has its printed order,
without a G3 premise or assumed successful full-window phase. -/
theorem initial_full_XR_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
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
    (hG₄₁ : (algorithmInitialState P f G x₀ bounds).descentConstant <
      dimensionDescentConstant (n+1) mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant (n+1) mu sigma upper ell <
      (algorithmInitialState P f G x₀ bounds).normConstant)
    (hoff : P.valuesEnabled = false)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center = krylov.Reference.cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center ∈ S) (hn : S ∈ 𝓝 center) {L₁ : ℝ≥0}
    (hHL : LipschitzOnWith L₁ H S)
    (hGS : ∀ z ∈ S, HasFDerivAt G (H z) z) :
    HasROrder (fun k => ‖(metricCoordinates base hb)
      ((algorithmRun P f G x₀ bounds k).point - center)‖) (oneGradientRoot (n+2)) := by
  obtain ⟨D⟩ := selectedGrowthSource_exists_of_initial_full P hP hfull f G H x₀ center bounds
    hF hG hHC radius hradius L hLip mu sigma upper ell trialUpper eta
    hmu hsigma hupper hell htrialUpper heta hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
  have hmax : P.maximumCapacity = n+1 := by
    have := hP.2.1
    have := hP.2.2.1
    omega
  exact selected_source_full_XR_physical_rorder P f G H x₀ center bounds D hP hoff hmax
    base hb hbase S hS hc hn hHL hGS

/-- XR-F with initially full memory has its improved physical order from
actual C3,1 data, genuine endpoint values and the original source assumptions. -/
theorem initial_full_XRF_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
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
      ((algorithmRun P f G x₀ bounds k).point - center)‖) (oneGradientRoot (n+1)) := by
  obtain ⟨D⟩ := selectedGrowthSource_exists_of_initial_full P hP hfull f G H x₀ center bounds
    hF hG hHC radius hradius L hLip mu sigma upper ell trialUpper eta
    hmu hsigma hupper hell htrialUpper heta hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
  have hmax : P.maximumCapacity = n+1 := by
    have := hP.2.1
    have := hP.2.2.1
    omega
  exact selected_source_full_XRF_physical_rorder P f G H x₀ center bounds D hP hon hmax
    base hb hbase S hS hc hn hHL hfS hGS T₃ hT hTLip

end
end krylov.XR

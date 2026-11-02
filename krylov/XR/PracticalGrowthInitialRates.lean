import krylov.XR.PracticalGrowthRates

/-!
# Initially full practical XR: rates without G3

Article Theorem 7.3 and Corollary 7.4. Positive actual observations fill the
initially full window before the selected source is constructed; partial
trial adequacy is consequently vacuous. These statements refer to the
actual practical execution and its original local analytic data.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Nonlinear krylov.Convergence
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Ordinary literal XR with initially full memory has its printed order,
without a G3 premise or assumed successful full-window phase. -/
theorem practical_initial_full_XR_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
    (hfull : P.initialCapacity = (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper ell trialUpper eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (heta : 0 < eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := practicalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (practicalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ none).descentConstant <
      dimensionDescentConstant (n+1) mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant (n+1) mu sigma upper ell <
      (algorithmInitialState P f G x₀ none).normConstant)
    (hoff : P.valuesEnabled = false)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center = krylov.Reference.cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center ∈ S) (hn : S ∈ 𝓝 center) {L₁ : ℝ≥0}
    (hHL : LipschitzOnWith L₁ H S)
    (hGS : ∀ z ∈ S, HasFDerivAt G (H z) z) :
    HasROrder (fun k => ‖(metricCoordinates base hb)
      ((practicalRun P f G x₀ k).point - center)‖) (oneGradientRoot (n+2)) := by
  obtain ⟨D⟩ := practicalGrowthSource_exists_of_initial_full P hP hfull f G H x₀ center
    hF hG hHC radius hradius L hLip mu sigma upper ell trialUpper eta
    hmu hsigma hupper hell htrialUpper heta hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
  have hmax : P.maximumCapacity = n+1 := by
    have := hP.2.1
    have := hP.2.2.1
    omega
  exact practical_source_full_XR_physical_rorder P f G H x₀ center D hP hoff hmax
    base hb hbase S hS hc hn hHL hGS

/-- XR-F with initially full memory has its improved physical order from
actual C3,1 data, genuine endpoint values and the original source assumptions. -/
theorem practical_initial_full_XRF_physical_rorder (P : Parameters) (hP : P.Valid (n+1))
    (hfull : P.initialCapacity = (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper ell trialUpper eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (heta : 0 < eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := practicalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (practicalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ none).descentConstant <
      dimensionDescentConstant (n+1) mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant (n+1) mu sigma upper ell <
      (algorithmInitialState P f G x₀ none).normConstant)
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
      ((practicalRun P f G x₀ k).point - center)‖) (oneGradientRoot (n+1)) := by
  obtain ⟨D⟩ := practicalGrowthSource_exists_of_initial_full P hP hfull f G H x₀ center
    hF hG hHC radius hradius L hLip mu sigma upper ell trialUpper eta
    hmu hsigma hupper hell htrialUpper heta hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
  have hmax : P.maximumCapacity = n+1 := by
    have := hP.2.1
    have := hP.2.2.1
    omega
  exact practical_source_full_XRF_physical_rorder P f G H x₀ center D hP hon hmax
    base hb hbase S hS hc hn hHL hfS hGS T₃ hT hTLip


/-- A valid full-window safeguard constant, fixed using only dimension,
limiting Hessian bounds and normalized incoming independence. -/
def fullWindowDescentConstant (dimension : ℕ) (mu sigma upper : ℝ) : ℝ :=
  dimensionDescentConstant dimension mu sigma upper upper

/-- The matching full-window length constant has no missing-direction
curvature parameter. -/
def fullWindowNormConstant (dimension : ℕ) (mu sigma upper : ℝ) : ℝ :=
  dimensionNormConstant dimension mu sigma upper mu

/-- Article Theorem 7.3 / Corollary 7.4, initially-full branch with original
G1, G2 and G4 only. The displayed safeguard constants depend solely on
physical problem data. The proof sets auxiliary partial-trial bounds to
`mu` and `upper` after full entry has been derived; no G3 premise is used. -/
theorem practical_initial_full_XR_original_rorder (P : Parameters) (hP : P.Valid (n+1))
    (hfull : P.initialCapacity = (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := practicalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (practicalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ none).descentConstant <
      fullWindowDescentConstant (n+1) mu sigma upper)
    (hG₄₂ : fullWindowNormConstant (n+1) mu sigma upper <
      (algorithmInitialState P f G x₀ none).normConstant)
    (hoff : P.valuesEnabled = false)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (hbase : H center = krylov.Reference.cgOperator base)
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (hc : center ∈ S) (hn : S ∈ 𝓝 center) {L₁ : ℝ≥0}
    (hHL : LipschitzOnWith L₁ H S)
    (hGS : ∀ z ∈ S, HasFDerivAt G (H z) z) :
    HasROrder (fun k => ‖(metricCoordinates base hb)
      ((practicalRun P f G x₀ k).point - center)‖) (oneGradientRoot (n+2)) := by
  exact practical_initial_full_XR_physical_rorder P hP hfull f G H x₀ center hF hG hHC radius hradius L hLip
    mu sigma upper mu upper 1 hmu hsigma hupper hmu hupper (by norm_num)
    hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
    hoff base hb hbase S hS hc hn hHL hGS

/-- Article Theorem 7.3 / Corollary 7.4, initially-full branch with original
G1, G2 and G4 only. The displayed safeguard constants depend solely on
physical problem data. The proof sets auxiliary partial-trial bounds to
`mu` and `upper` after full entry has been derived; no G3 premise is used. -/
theorem practical_initial_full_XRF_original_rorder (P : Parameters) (hP : P.Valid (n+1))
    (hfull : P.initialCapacity = (n+1))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (x₀ center : EuclideanSpace ℝ (Fin (n+1)))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := practicalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (practicalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ none).descentConstant <
      fullWindowDescentConstant (n+1) mu sigma upper)
    (hG₄₂ : fullWindowNormConstant (n+1) mu sigma upper <
      (algorithmInitialState P f G x₀ none).normConstant)
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
      ((practicalRun P f G x₀ k).point - center)‖) (oneGradientRoot (n+1)) := by
  exact practical_initial_full_XRF_physical_rorder P hP hfull f G H x₀ center hF hG hHC radius hradius L hLip
    mu sigma upper mu upper 1 hmu hsigma hupper hmu hupper (by norm_num)
    hpositive hHnorm hconv hne K₀ hgain hprobeGain hG₄₁ hG₄₂
    hon base hb hbase S hS hc hn hHL hGS hfS T₃ hT hTLip


end
end krylov.XR

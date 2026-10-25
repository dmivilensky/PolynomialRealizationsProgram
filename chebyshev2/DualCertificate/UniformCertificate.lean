import chebyshev2.DualCertificate.AdmissibilityStability
import chebyshev2.DualCertificate.ValueContinuity
import chebyshev2.DualCertificate.UniformTransfer

/-!
Article: chebyshev2, Theorem 3.6.
Theorem 3.6(ii) and E.1 for literal rational certificate data.
Result: `chebyshev2.DualCertificate.Data.gainConstant_ge_value` supplies the stated article
conclusion.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set Filter Real chebyshev2.Packing chebyshev2.Calibration.Data
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
 /--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
A.value (packedCoupling_positive (J n).val (by omega) (J n).property) (packedLogDeterminant (J
n).val (by omega) (J n).property 32) (packedLogDeterminant (J n).val (by omega) (J n).property
64) (packedLogDeterminant (J n).val (by omega) (J n).property
(A.calibration.sigma*packedCoupling (J n).val (by omega) (J n).property)) ((packedCoupling (J
n).val (by omega) (J n).property)^2/4* ∑' j,packedEigenvalue (J n).val (by omega) (J
n).property j^2)) atTop (𝓝 A.targetValue)`.

Use: `chebyshev2.DualCertificate.Data.packed_value_tendsto` uses this limit to establish
the limit stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.packedCoupling_positive`,
`chebyshev2.Calibration.Data.packedCoupling_tendsto`,
`chebyshev2.DualCertificate.packed_fixed_observation_tendsto` with the arguments shown in
the proof.
-/
theorem AnalyticData.packed_value_tendsto_of_continuous (A : AnalyticData)
    (hc : Continuous (fun p : Data.ObservationDomain =>
      A.value p.1.property p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) (J : ∀ n : ℕ,chebyshev2.Fiber (n+1)) :
    Tendsto (fun n => A.value (packedCoupling_positive (J n).val (by omega) (J n).property)
      (packedLogDeterminant (J n).val (by omega) (J n).property 32)
      (packedLogDeterminant (J n).val (by omega) (J n).property 64)
      (packedLogDeterminant (J n).val (by omega) (J n).property
        (A.calibration.sigma*packedCoupling (J n).val (by omega) (J n).property))
      ((packedCoupling (J n).val (by omega) (J n).property)^2/4*
        ∑' j,packedEigenvalue (J n).val (by omega) (J n).property j^2)) atTop (𝓝 A.targetValue) := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.packedCoupling_positive`,
  -- `chebyshev2.Calibration.Data.packedCoupling_tendsto`,
  -- `chebyshev2.DualCertificate.packed_fixed_observation_tendsto` with the arguments shown
  -- in the proof.
  let k : Ioi (0:ℝ) := ⟨Real.pi^2/4,div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)⟩
  -- Record the convergence hk with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hk : Tendsto (fun n => (⟨packedCoupling (J n).val (by omega) (J n).property,
      packedCoupling_positive (J n).val (by omega) (J n).property⟩ : Ioi (0:ℝ))) atTop (𝓝 k) :=
    tendsto_subtype_rng.mpr (chebyshev2.Calibration.Data.packedCoupling_tendsto J)
  have h₀ := packed_fixed_observation_tendsto J (by norm_num : (0:ℝ)≤32)
  have h₁ := packed_fixed_observation_tendsto J (by norm_num : (0:ℝ)≤64)
  have hσ := A.calibration.packedObservation_tendsto J
  have hS := packed_S_tendsto J
  have hp := hk.prodMk_nhds (h₀.prodMk_nhds (h₁.prodMk_nhds (hσ.prodMk_nhds hS)))
  have hv := (hc.continuousAt (x := (k,log (cosh (sqrt 32)),log (cosh (sqrt 64)),
    log (cosh (sqrt (A.calibration.sigma*(Real.pi^2/4)))),(Real.pi^2/4)^2/6))).tendsto
  have h := hv.comp hp
  exact h

namespace Data
variable (D : chebyshev2.DualCertificate.Data)
 /--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
D.analytic.value (packedCoupling_positive (J n).val (by omega) (J n).property)
(packedLogDeterminant (J n).val (by omega) (J n).property 32) (packedLogDeterminant (J n).val
(by omega) (J n).property 64) (packedLogDeterminant (J n).val (by omega) (J n).property
(D.calibration.sigma*packedCoupling (J n).val (by omega) (J n).property)) ((packedCoupling (J
n).val (by omega) (J n).property)^2/4* ∑' j,packedEigenvalue (J n).val (by omega) (J
n).property j^2)) atTop (𝓝 D.analytic.targetValue)`.

Use: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` uses this limit to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop,∀ J :
chebyshev2.Fiber (n+1),D.analytic.targetValue-ε≤J.val.normalizedEnergy`.

Article: chebyshev2, Theorem E.1.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.AnalyticData.packed_value_tendsto_of_continuous`,
`chebyshev2.DualCertificate.Data.value_continuous` with the arguments shown in the proof.
-/
theorem packed_value_tendsto (J : ∀ n : ℕ,chebyshev2.Fiber (n+1)) :
    Tendsto (fun n => D.analytic.value (packedCoupling_positive (J n).val (by omega) (J n).property)
      (packedLogDeterminant (J n).val (by omega) (J n).property 32)
      (packedLogDeterminant (J n).val (by omega) (J n).property 64)
      (packedLogDeterminant (J n).val (by omega) (J n).property
        (D.calibration.sigma*packedCoupling (J n).val (by omega) (J n).property))
      ((packedCoupling (J n).val (by omega) (J n).property)^2/4*
        ∑' j,packedEigenvalue (J n).val (by omega) (J n).property j^2)) atTop (𝓝 D.analytic.targetValue) :=
  D.analytic.packed_value_tendsto_of_continuous D.value_continuous J

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop,∀ J :
chebyshev2.Fiber (n+1),D.analytic.targetValue-ε≤J.val.normalizedEnergy`.

Use: `chebyshev2.DualCertificate.Data.gainConstant_ge_value` uses this bound to establish
the stated quantitative bound `2*sqrt
D.analytic.targetValue≤chebyshev2.Optimal.gainConstant I`.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates `chebyshev2.DualCertificate.Data.admissible_stable`,
`chebyshev2.DualCertificate.Data.admissible_analytic`,
`chebyshev2.DualCertificate.AnalyticData.uniform_finite_lower_bound` with the arguments
shown in the proof.
-/
theorem uniform_finite_lower_bound
    (ha : D.Admissible (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop,∀ J : chebyshev2.Fiber (n+1),D.analytic.targetValue-ε≤J.val.normalizedEnergy := by
  have hs := D.admissible_stable (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)) ha
  have hs' : ∀ᶠ κ in 𝓝 (Real.pi^2/4),∀ hκ : 0<κ,D.analytic.Admissible hκ :=
    hs.mono (fun _ h hκ => D.admissible_analytic hκ (h hκ))
  exact D.analytic.uniform_finite_lower_bound hs' (D.packed_value_tendsto) hε

 /--
The stated quantitative bound `D.analytic.targetValue≤chebyshev2.Optimal.greenConstant`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.greenConstant_ge_of_uniform`,
`chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` with the arguments shown in
the proof.
-/
theorem greenConstant_ge_value
    (ha : D.Admissible (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))) :
    D.analytic.targetValue≤chebyshev2.Optimal.greenConstant :=
  greenConstant_ge_of_uniform (fun _ hε => D.uniform_finite_lower_bound ha hε)

 /--
The stated quantitative bound `2*sqrt
D.analytic.targetValue≤chebyshev2.Optimal.gainConstant I`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 3.6.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.gainConstant_ge_of_uniform`,
`chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` with the arguments shown in
the proof.
-/
theorem gainConstant_ge_value
    (ha : D.Admissible (κ := Real.pi^2/4) (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)))
    (I : chebyshev1.SpectralInterval) :
    2*sqrt D.analytic.targetValue≤chebyshev2.Optimal.gainConstant I :=
  gainConstant_ge_of_uniform (fun _ hε => D.uniform_finite_lower_bound ha hε) I

end Data
end
end chebyshev2.DualCertificate

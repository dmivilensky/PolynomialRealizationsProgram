import «2610.05164v2».Residual.LevelSets
import «2610.05164v2».Calibration.BaseIdentity

/-!
Article: 2610.05164v2, Proposition 8.
E.2's price identity for bounded, piecewise continuous prices and nonmonotone ground coordinates.
Use: `«2610.05164v2».Residual.priceCost` feeds
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` (Proposition 8, including the endpoint
condition at zero amplitude).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Residual
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
A uniformly bounded scalar price that is continuous away from finitely many exceptional points.
This suffices for the integrated residual identity despite cell-boundary discontinuities.

Use: `«2610.05164v2».Residual.Price.antiderivative` uses this record of data and proof
obligations in the displayed construction of `antiderivative`. Its inputs and component
formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
structure Price where
  /-- Piecewise regular scalar price. -/
  value : ℝ → ℝ
  /-- Finite exceptional set at which continuity is not required. -/
  exceptional : Finset ℝ
  /-- Continuity away from the finitely many exceptional points. -/
  continuous : ∀ q ∉ exceptional, ContinuousAt value q
  /-- Uniform finite norm bound for the price. -/
  B : ℝ
  /-- The proposed uniform bound is nonnegative. -/
  bound_nonneg : 0 ≤ B
  /-- The price norm never exceeds B, enabling integrability along the density flow. -/
  bound : ∀ q, ‖value q‖ ≤ B

namespace Price
variable (P : Price)

/--
Measurability of the displayed map: `Measurable P.value`.

Use: `«2610.05164v2».Residual.Price.antiderivative_regular` uses this measurability result to
establish the actual derivative at the stated point: `HasDerivAt P.antiderivative (P.value q)
q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem measurable : Measurable P.value := by
  apply measurable_of_countable_not_continuousAt
  apply P.exceptional.countable_toSet.mono
  intro q hq
  exact not_not.mp (fun h => hq (P.continuous q h))

/--
The precise assertion is `IntervalIntegrable P.value volume a b`.

Use: `«2610.05164v2».Residual.Price.antiderivative_lipschitz` rewrites with this assertion to
establish the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal P.B) P.antiderivative`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.Price.measurable` with the
arguments shown in the proof.
-/
theorem intervalIntegrable (a b : ℝ) : IntervalIntegrable P.value volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply (integrableOn_const (C := P.B) (s := uIcc a b) isCompact_uIcc.measure_ne_top).mono'
    P.measurable.aestronglyMeasurable
  exact Eventually.of_forall P.bound

/--
Defines `antiderivative` of type `ℝ → ℝ` by `primitive P.value`.

Use: `«2610.05164v2».Residual.Price.antiderivative_lipschitz` uses this definition to establish
the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal P.B) P.antiderivative`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def antiderivative : ℝ → ℝ := primitive P.value

/--
The displayed Lipschitz bound: `LipschitzWith (Real.toNNReal P.B) P.antiderivative`.

Use: `«2610.05164v2».Residual.Price.chain_rule` uses this assertion to establish establishes
the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x => P.antiderivative
(q x)) (P.value (q x)*d x) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.Price.intervalIntegrable` with the
arguments shown in the proof.
-/
theorem antiderivative_lipschitz : LipschitzWith (Real.toNNReal P.B) P.antiderivative := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,← Real.norm_eq_abs,Real.toNNReal_of_nonneg P.bound_nonneg]
  change ‖(∫ t in (0:ℝ)..x, P.value t)-(∫ t in (0:ℝ)..y, P.value t)‖ ≤ P.B*|x-y|
  rw [intervalIntegral.integral_interval_sub_left (P.intervalIntegrable 0 x) (P.intervalIntegrable 0 y)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => P.bound t)

/--
The actual derivative at the stated point: `HasDerivAt P.antiderivative (P.value q) q`.

Use: `«2610.05164v2».Residual.Price.chain_rule` uses this derivative formula to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x =>
P.antiderivative (q x)) (P.value (q x)*d x) x`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem antiderivative_regular (q : ℝ) (hq : q ∉ P.exceptional) :
    HasDerivAt P.antiderivative (P.value q) q :=
  intervalIntegral.integral_hasDerivAt_right (P.intervalIntegrable 0 q)
    P.measurable.stronglyMeasurable.stronglyMeasurableAtFilter (P.continuous q hq)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun x =>
P.antiderivative (q x)) (P.value (q x)*d x) x`.

Use: `«2610.05164v2».Residual.Price.integral_chain` uses this identity to establish exact
identity `(∫ x, P.value (q x)*d x)=∫ t in lo..hi, P.value t`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.finite_exception_chain_rule`,
`«2610.05164v2».Residual.Price.antiderivative_lipschitz`,
`«2610.05164v2».Residual.Price.antiderivative_regular` with the arguments shown in the proof.
-/
theorem chain_rule {q d : ℝ → ℝ} (hq : ∀ a b, AbsolutelyContinuousOnInterval q a b)
    (hd : ∀ᵐ x, HasDerivAt q (d x) x) :
    ∀ᵐ x, HasDerivAt (fun x => P.antiderivative (q x)) (P.value (q x)*d x) x :=
  finite_exception_chain_rule hq hd P.antiderivative_lipschitz P.exceptional P.antiderivative_regular

/--
The signed price integral depends only on the two endpoint values of q.

Exact identity `(∫ x, P.value (q x)*d x)=∫ t in lo..hi, P.value t`.

Use: `«2610.05164v2».Residual.Price.ground_price_identity` uses this identity to establish the
precise assertion is `(∫ x, P.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))= ∫ q in
(0:ℝ)..2, P.value q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem integral_chain {q d : ℝ → ℝ} {lo hi : ℝ}
    (hq : ∀ a b, AbsolutelyContinuousOnInterval q a b)
    (hd : ∀ᵐ x, HasDerivAt q (d x) x) (hint : Integrable d)
    (hl : Tendsto q atBot (𝓝 lo)) (hr : Tendsto q atTop (𝓝 hi)) :
    (∫ x, P.value (q x)*d x)=∫ t in lo..hi, P.value t := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  have hc := «2610.05164v2».GroundState.locallyAC_continuous hq
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi' : Integrable (fun x => P.value (q x)*d x) :=
    hint.bdd_mul (P.measurable.comp hc.measurable).aestronglyMeasurable (Eventually.of_forall (fun x => P.bound _))
  have h := integral_derivative_eq_limits
    (fun a b => P.antiderivative_lipschitz.comp_absolutelyContinuousOnInterval (hq a b))
    (P.chain_rule hq hd) hi'
    (P.antiderivative_lipschitz.continuous.continuousAt.tendsto.comp hl)
    (P.antiderivative_lipschitz.continuous.continuousAt.tendsto.comp hr)
  rw [h]
  exact intervalIntegral.integral_interval_sub_left (P.intervalIntegrable 0 hi) (P.intervalIntegrable 0 lo)

/--
The precise assertion is `(∫ x, P.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))= ∫ q in
(0:ℝ)..2, P.value q`.

Use: `«2610.05164v2».Calibration.Data.flowResidual_integral` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.Price.integral_chain`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_locallyAC`,
`«2610.05164v2».GroundState.GroundWitness.coordinate_derivative` with the arguments shown in
the proof.
-/
theorem ground_price_identity {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
    (G : GroundWitness hm hn) :
    (∫ x, P.value (G.q x)*(groundParameter hm hn*m x-Q (G.q x)))=
      ∫ q in (0:ℝ)..2, P.value q :=
  P.integral_chain G.coordinate_locallyAC G.coordinate_derivative G.coordinate_integrability.2
    G.coordinate_limits.1 G.coordinate_limits.2

end Price

/--
Defines `priceCost` of type `ℝ` by `(∫ q in (0:ℝ)..2, η q)/κ+τ*(κ-2)/κ`.

Use: `«2610.05164v2».Residual.priceCost_gauge` uses this definition to establish the identity
`priceCost κ τ (fun q => η q+κ*deriv F q)=priceCost κ τ η`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def priceCost (κ τ : ℝ) (η : ℝ → ℝ) : ℝ :=
  (∫ q in (0:ℝ)..2, η q)/κ+τ*(κ-2)/κ

/--
Exact identity `priceCost κ τ (fun q => η q+κ*deriv F q)=priceCost κ τ η`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 8.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem priceCost_gauge (κ τ : ℝ) {η F : ℝ → ℝ}
    (hη : IntervalIntegrable η volume 0 2) (hF : ContDiff ℝ 1 F) (hend : F 0=F 2) :
    priceCost κ τ (fun q => η q+κ*deriv F q)=priceCost κ τ η := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hi : IntervalIntegrable (deriv F) volume 0 2 :=
    (hF.continuous_deriv (by norm_num)).intervalIntegrable 0 2
  have he : (∫ q in (0:ℝ)..2, deriv F q)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _ => (hF.differentiable (by norm_num) q).hasDerivAt) hi,hend,sub_self]
  unfold priceCost
  rw [intervalIntegral.integral_add hη (hi.const_mul κ),intervalIntegral.integral_const_mul,he]
  simp

end
end «2610.05164v2».Residual

import chebyshev2.GroundState.Uniqueness

/-!
Article: chebyshev2, Theorem 3.1.
Both finite limits of the actual ground coordinate exist.
Use: `chebyshev2.GroundState.RiccatiData.q_limits_exist` feeds
`chebyshev2.GroundState.RiccatiData.q_endpoint_limits` (q endpoint limits).
Proof chain: `chebyshev2.GroundState.GroundWitness.coordinate_limits` — chebyshev2, Theorem
3.1; Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

namespace RiccatiData
variable {m : ℝ → ℝ} {c : ℝ} (R : RiccatiData m c)

/--
Defines `q` of type `ℝ` by `1-R.a x`.

Use: `chebyshev2.GroundState.RiccatiData.Q` uses this definition in the displayed
construction of `Q`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.
-/
def q (x : ℝ) : ℝ := 1-R.a x
/--
Defines `Q` of type `ℝ` by `R.q x*(2-R.q x)`.

Use: `chebyshev2.GroundState.RiccatiData.Q_integrable` uses this definition to establish
integrability of the displayed function: `Integrable R.Q`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.
-/
def Q (x : ℝ) : ℝ := R.q x*(2-R.q x)

/--
Membership in the specified domain/enclosure: `R.q x ∈ Icc (0:ℝ) 2`.

Use: `chebyshev2.GroundState.RiccatiData.Q_integrable` uses this assertion to establish
integrability of the displayed function: `Integrable R.Q`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem q_mem (x : ℝ) : R.q x ∈ Icc (0:ℝ) 2 := by
  have hb := abs_le.mp (R.bound x)
  constructor <;> dsimp [q] <;> linarith

/--
The stated quantitative bound `0 ≤ R.Q x`.

Use: `chebyshev2.GroundState.RiccatiData.Q_integrable` uses this bound to establish
integrability of the displayed function: `Integrable R.Q`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_mem` with the
arguments shown in the proof.
-/
theorem Q_nonneg (x : ℝ) : 0 ≤ R.Q x :=
  mul_nonneg (R.q_mem x).1 (sub_nonneg.mpr (R.q_mem x).2)

/--
Continuity of the displayed function: `Continuous R.q`.

Use: `chebyshev2.GroundState.RiccatiData.Q_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous R.Q`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.continuous` with
the arguments shown in the proof.
-/
theorem q_continuous : Continuous R.q := continuous_const.sub R.continuous
/--
Continuity of the displayed function: `Continuous R.Q`.

Use: `chebyshev2.GroundState.RiccatiData.Q_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable R.Q`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_continuous` with
the arguments shown in the proof.
-/
theorem Q_continuous : Continuous R.Q := R.q_continuous.mul (continuous_const.sub R.q_continuous)

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval R.q a b`.

Use: `chebyshev2.GroundState.RiccatiData.Q_interval_identity` uses this assertion to
establish exact identity `(∫ x in a..b, R.Q x)=c*(∫ x in a..b, m x)-R.q b+R.q a`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem q_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval R.q a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => (1:ℝ)) (uIcc a b)).absolutelyContinuousOnInterval
  apply (hc.sub (R.locally_ac a b)).congr
  intro x _
  rfl

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt R.q (c*m x-R.Q
x) x`.

Use: `chebyshev2.GroundState.RiccatiData.Q_interval_identity` uses this assertion to
establish exact identity `(∫ x in a..b, R.Q x)=c*(∫ x in a..b, m x)-R.q b+R.q a`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.RiccatiData.q_lipschitz`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_derivative_ae : ∀ᵐ x, HasDerivAt R.q (c*m x-R.Q x) x := by
  filter_upwards [R.derivative_ae] with x hx
  have hd : HasDerivAt R.q (0-(1-c*m x-R.a x^2)) x := (hasDerivAt_const x (1:ℝ)).sub hx
  convert hd using 1
  change c*m x-(1-R.a x)*(2-(1-R.a x))=0-(1-c*m x-R.a x^2)
  ring

/--
Exact identity `(∫ x in a..b, R.Q x)=c*(∫ x in a..b, m x)-R.q b+R.q a`.

Use: `chebyshev2.GroundState.RiccatiData.Q_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable R.Q`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.Q_continuous`,
`chebyshev2.Sobolev.locallyAC_integral_eq_sub`,
`chebyshev2.GroundState.RiccatiData.q_locallyAC` with the arguments shown in the proof.
-/
theorem Q_interval_identity (hm : Integrable m) (a b : ℝ) :
    (∫ x in a..b, R.Q x)=c*(∫ x in a..b, m x)-R.q b+R.q a := by
  have hd : IntervalIntegrable (fun x => c*m x-R.Q x) volume a b :=
    (hm.intervalIntegrable.const_mul c).sub (R.Q_continuous.intervalIntegrable a b)
  have h := locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae a b
  rw [intervalIntegral.integral_sub (hm.intervalIntegrable.const_mul c)
    (R.Q_continuous.intervalIntegrable a b), intervalIntegral.integral_const_mul] at h
  linarith

/--
The finite interval identity gives global integrability of q(2-q), without assuming
integrability or endpoint limits of q.

Integrability of the displayed function: `Integrable R.Q`.

Use: `chebyshev2.GroundState.RiccatiData.q_derivative_integrable` uses this integrability
result to establish integrability of the displayed function: `Integrable (fun x => c*m x-R.Q
x)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem Q_integrable (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : 0 ≤ c) : Integrable R.Q := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply integrable_of_intervalIntegral_norm_bounded (c*(∫ x, m x)+2)
    (a := fun r : ℝ => -r) (b := fun r : ℝ => r) (l := atTop)
  · intro r
    exact (R.Q_continuous.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · exact tendsto_neg_atTop_atBot
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    have hab : -r ≤ r := by linarith
    have hmle : (∫ x in -r..r, m x) ≤ ∫ x, m x := by
      rw [intervalIntegral.integral_of_le hab]
      exact setIntegral_le_integral hm (Filter.Eventually.of_forall hn)
    have he : (fun x => ‖R.Q x‖)=R.Q := funext (fun x => Real.norm_of_nonneg (R.Q_nonneg x))
    rw [he,R.Q_interval_identity hm]
    have h0 := (R.q_mem r).1
    have h2 := (R.q_mem (-r)).2
    have hle := mul_le_mul_of_nonneg_left hmle hc
    linarith

/--
Integrability of the displayed function: `Integrable (fun x => c*m x-R.Q x)`.

Use: `chebyshev2.GroundState.RiccatiData.q_limits_exist` uses this integrability result to
establish constructs witnesses with the exact properties `∃ lo hi : ℝ, Tendsto R.q atBot (𝓝 lo)
∧ Tendsto R.q atTop (𝓝 hi)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.Q_integrable` with
the arguments shown in the proof.
-/
theorem q_derivative_integrable (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : 0 ≤ c) :
    Integrable (fun x => c*m x-R.Q x) := (hm.const_mul c).sub (R.Q_integrable hm hn hc)

/--
Both finite limits of the actual ground coordinate exist.

Constructs witnesses with the exact properties `∃ lo hi : ℝ, Tendsto R.q atBot (𝓝 lo) ∧ Tendsto
R.q atTop (𝓝 hi)`.

Use: `chebyshev2.GroundState.RiccatiData.q_endpoint_limits` uses this assertion to
establish convergence along the specified source filter to the specified limit: `Tendsto R.q
atBot (𝓝 0) ∧ Tendsto R.q atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.RiccatiData.q_derivative_integrable`,
`chebyshev2.Sobolev.locallyAC_integral_eq_sub`,
`chebyshev2.GroundState.RiccatiData.q_locallyAC` with the arguments shown in the proof.
-/
theorem q_limits_exist (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : 0 ≤ c) :
    ∃ lo hi : ℝ, Tendsto R.q atBot (𝓝 lo) ∧ Tendsto R.q atTop (𝓝 hi) := by
  -- Use the identities/estimates
  -- `chebyshev2.GroundState.RiccatiData.q_derivative_integrable`,
  -- `chebyshev2.Sobolev.locallyAC_integral_eq_sub`,
  -- `chebyshev2.GroundState.RiccatiData.q_locallyAC` with the arguments shown in the
  -- proof.
  let d : ℝ → ℝ := fun x => c*m x-R.Q x
  -- Establish hd as the integrability justification for the later integral estimates or
  -- changes of order.
  have hd : Integrable d := R.q_derivative_integrable hm hn hc
  refine ⟨R.q 0-∫ x in Iic (0:ℝ), d x,R.q 0+∫ x in Ioi (0:ℝ), d x,?_,?_⟩
  · have he (x : ℝ) : R.q 0-(∫ t in x..(0:ℝ), d t)=R.q x := by
      rw [locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae]
      ring
    simpa only [id_eq,he] using
      (intervalIntegral_tendsto_integral_Iic 0 hd.integrableOn tendsto_id).const_sub (R.q 0)
  · have he (x : ℝ) : R.q 0+(∫ t in (0:ℝ)..x, d t)=R.q x := by
      rw [locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae]
      ring
    simpa only [id_eq,he] using
      (intervalIntegral_tendsto_integral_Ioi 0 hd.integrableOn tendsto_id).const_add (R.q 0)

end RiccatiData
end
end chebyshev2.GroundState

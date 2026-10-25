import chebyshev2.Calibration.AmplitudeBounds
import chebyshev2.Calibration.ChainRule

/-!
Article: chebyshev2, Proposition 4.
The calibration filter in (14), and the literal potential in (17).
Use: `chebyshev2.Calibration.Data.calibration_identity` feeds
`chebyshev2.Calibration.Data.calibration_identity_ae` (calibration identity ae).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.GroundState chebyshev2.Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
Defines `Jprime` of type `ℝ` by `-C.potential h/(2+C.sigma*C.potential h)`.

Use: `chebyshev2.Calibration.Data.J` uses this definition in the displayed construction of
`J`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def Jprime (h : ℝ) : ℝ := -C.potential h/(2+C.sigma*C.potential h)
/--
Defines `J` of type `ℝ → ℝ` by `primitive C.Jprime`.

Use: `chebyshev2.Calibration.Data.J_zero` rewrites with this definition to establish exact
identity `C.J 0=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def J : ℝ → ℝ := primitive C.Jprime

/--
Continuity of the displayed function: `Continuous C.Jprime`.

Use: `chebyshev2.Calibration.Data.J_c1` uses this continuity result to establish smoothness
to the stated order: `ContDiff ℝ 1 C.J`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.potential_continuous`,
`chebyshev2.Calibration.Data.denominator_positive` with the arguments shown in the proof.
-/
theorem Jprime_continuous : Continuous C.Jprime :=
  C.potential_continuous.neg.div
    (continuous_const.add (continuous_const.mul C.potential_continuous))
    (fun h => (C.denominator_positive h).ne')

/--
Smoothness to the stated order: `ContDiff ℝ 1 C.J`.

Use: `chebyshev2.Calibration.Data.J_composition_mass` uses this assertion to establish
exact identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.primitive_c1`,
`chebyshev2.Calibration.Data.Jprime_continuous` with the arguments shown in the proof.
-/
theorem J_c1 : ContDiff ℝ 1 C.J := primitive_c1 C.Jprime_continuous
/--
The actual derivative at the stated point: `HasDerivAt C.J (C.Jprime h) h`.

Use: `chebyshev2.Calibration.Data.calibration_identity_ae` uses this derivative formula to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x,
(C.calibrationFilter hm hn x)^2+deriv (fun x => C.J (C.calibrationState G x)) x= C.F (G.q x)
(C.calibrationState G x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.primitive_derivative`,
`chebyshev2.Calibration.Data.Jprime_continuous` with the arguments shown in the proof.
-/
theorem J_derivative (h : ℝ) : HasDerivAt C.J (C.Jprime h) h := primitive_derivative C.Jprime_continuous h
/--
Exact identity `C.J 0=0`.

Use: `chebyshev2.Calibration.Data.J_composition_mass` uses this identity to establish exact
identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm
hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem J_zero : C.J 0=0 := by simp [J,primitive]

/--
The stated quantitative bound `‖C.Jprime h‖ ≤ 1`.

Use: `chebyshev2.Calibration.Data.J_composition_integrable` uses this bound to establish
integrability of the displayed function: `Integrable (fun x => C.Jprime (C.calibrationState G
x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.clamp_mem`,
`chebyshev2.Calibration.Data.potential_nonneg`,
`chebyshev2.Calibration.Data.denominator_positive` with the arguments shown in the proof.
-/
theorem Jprime_bound (h : ℝ) : ‖C.Jprime h‖ ≤ 1 := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.clamp_mem`,
  -- `chebyshev2.Calibration.Data.potential_nonneg`,
  -- `chebyshev2.Calibration.Data.denominator_positive` with the arguments shown in the
  -- proof.
  have hg := C.bounds _ (clamp_mem h)
  have hn := C.potential_nonneg h
  have hle : C.potential h ≤ 2 := by
    unfold potential
    linarith [le_max_left (0:ℝ) (min 2 h)]
  rw [Jprime,norm_div,Real.norm_eq_abs,abs_neg,abs_of_nonneg hn,
    Real.norm_eq_abs,abs_of_pos (C.denominator_positive h)]
  apply (div_le_one (C.denominator_positive h)).2
  nlinarith [mul_nonneg C.sigma_positive.le hn]

/--
Defines `calibrationFilter` of type `ℝ` by `nonlinear (C.sigma*groundParameter hm hn) m
x/C.sigma`.

Use: `chebyshev2.Calibration.Data.calibrationFilter_derivative` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(C.calibrationFilter hm hn) (groundParameter hm hn*m x-2*C.calibrationFilter hm hn
x-C.sigma*(C.calibrationFilter hm hn x)^2) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def calibrationFilter {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (x : ℝ) : ℝ :=
  nonlinear (C.sigma*groundParameter hm hn) m x/C.sigma

/--
Defines `calibrationState` of type `ℝ` by `G.q x-C.calibrationFilter hm hn x`.

Use: `chebyshev2.Calibration.Data.calibrationState_derivative` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(C.calibrationState G) ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState
G x) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def calibrationState {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x}
    (G : GroundWitness hm hn) (x : ℝ) : ℝ := G.q x-C.calibrationFilter hm hn x

variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
include G

/--
Membership in the specified domain/enclosure: `C.calibrationFilter hm hn x ∈ Icc (0:ℝ) (G.q
x)`.

Use: `chebyshev2.Calibration.Data.calibrationState_bounds` uses this assertion to establish
membership in the specified domain/enclosure: `C.calibrationState G x ∈ Icc (0:ℝ) (G.q x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Filters.nonlinear_le_coordinate`, `chebyshev2.Filters.nonlinear_bounds`
with the arguments shown in the proof.
-/
theorem calibrationFilter_bounds (x : ℝ) : C.calibrationFilter hm hn x ∈ Icc (0:ℝ) (G.q x) := by
  -- Use the identities/estimates `chebyshev2.GroundState.GroundWitness.coupling_positive`,
  -- `chebyshev2.Filters.nonlinear_le_coordinate`,
  -- `chebyshev2.Filters.nonlinear_bounds` with the arguments shown in the proof.
  have hs := mul_nonneg C.sigma_positive.le G.coupling_positive.le
  have hb := nonlinear_le_coordinate G hs x
  constructor
  · exact div_nonneg (nonlinear_bounds hm hn hs x).1 C.sigma_positive.le
  · apply (div_le_iff₀ C.sigma_positive).2
    have he : C.sigma*groundParameter hm hn/groundParameter hm hn=C.sigma :=
      mul_div_cancel_right₀ _ G.coupling_positive.ne'
    rw [he] at hb
    linarith

/--
Membership in the specified domain/enclosure: `C.calibrationState G x ∈ Icc (0:ℝ) (G.q x)`.

Use: `chebyshev2.Calibration.Data.J_composition_mass` uses this assertion to establish
exact identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.calibrationFilter_bounds`
with the arguments shown in the proof.
-/
theorem calibrationState_bounds (x : ℝ) : C.calibrationState G x ∈ Icc (0:ℝ) (G.q x) := by
  have h := C.calibrationFilter_bounds G x
  exact ⟨sub_nonneg.mpr h.2,sub_le_self _ h.1⟩

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(C.calibrationFilter hm hn) a b`.

Use: `chebyshev2.Calibration.Data.calibrationState_locallyAC` uses this assertion to
establish absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(C.calibrationState G) a b`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.Filters.nonlinear_locallyAC` with the arguments shown in the proof.
-/
theorem calibrationFilter_locallyAC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (C.calibrationFilter hm hn) a b := by
  have hs := mul_nonneg C.sigma_positive.le G.coupling_positive.le
  apply ((nonlinear_locallyAC hm hn hs a b).const_mul (1/C.sigma)).congr
  intro x _
  dsimp [calibrationFilter]
  ring

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval
(C.calibrationState G) a b`.

Use: `chebyshev2.Calibration.Data.J_composition_integrable` uses this assertion to
establish integrability of the displayed function: `Integrable (fun x => C.Jprime
(C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn
x)^2-2*C.calibrationState G x))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coordinate_locallyAC`,
`chebyshev2.Calibration.Data.calibrationFilter_locallyAC` with the arguments shown in the
proof.
-/
theorem calibrationState_locallyAC (a b : ℝ) :
    AbsolutelyContinuousOnInterval (C.calibrationState G) a b :=
  (G.coordinate_locallyAC a b).sub (C.calibrationFilter_locallyAC G a b)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(C.calibrationFilter hm hn) (groundParameter hm hn*m x-2*C.calibrationFilter hm hn
x-C.sigma*(C.calibrationFilter hm hn x)^2) x`.

Use: `chebyshev2.Calibration.Data.calibrationState_derivative` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(C.calibrationState G) ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState
G x) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem calibrationFilter_derivative : ∀ᵐ x, HasDerivAt (C.calibrationFilter hm hn)
    (groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn x)^2) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [nonlinear_derivative hm hn (mul_nonneg C.sigma_positive.le G.coupling_positive.le)] with x hx
  have h := hx.div_const C.sigma
  change HasDerivAt (C.calibrationFilter hm hn)
    ((C.sigma*groundParameter hm hn*m x-2*nonlinear (C.sigma*groundParameter hm hn) m x-
      (nonlinear (C.sigma*groundParameter hm hn) m x)^2)/C.sigma) x at h
  convert h using 1
  unfold calibrationFilter
  field_simp [C.sigma_positive.ne']

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt
(C.calibrationState G) ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState
G x) x`.

Use: `chebyshev2.Calibration.Data.calibration_identity_ae` uses this assertion to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, (C.calibrationFilter hm
hn x)^2+deriv (fun x => C.J (C.calibrationState G x)) x= C.F (G.q x) (C.calibrationState G x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem calibrationState_derivative : ∀ᵐ x, HasDerivAt (C.calibrationState G)
    ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [G.coordinate_derivative,C.calibrationFilter_derivative G] with x hq hf
  have h := hq.sub hf
  change HasDerivAt (C.calibrationState G)
    ((groundParameter hm hn*m x-G.q x*(2-G.q x))-
      (groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn x)^2)) x at h
  convert h using 1
  unfold calibrationState
  ring

/--
Integrability of the displayed function: `Integrable (C.calibrationFilter hm hn)`.

Use: `chebyshev2.Calibration.Data.calibrationFilter_derivative_integrable` uses this
integrability result to establish integrability of the displayed function: `Integrable (fun x
=> groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn
x)^2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_integrable`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem calibrationFilter_integrable : Integrable (C.calibrationFilter hm hn) :=
  (nonlinear_integrable hm hn (mul_nonneg C.sigma_positive.le G.coupling_positive.le)).div_const _

/--
Integrability of the displayed function: `Integrable (fun x => (C.calibrationFilter hm hn
x)^2)`.

Use: `chebyshev2.Calibration.Data.calibrationFilter_derivative_integrable` uses this
integrability result to establish integrability of the displayed function: `Integrable (fun x
=> groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn
x)^2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_square_integrable`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem calibrationFilter_square_integrable : Integrable (fun x => (C.calibrationFilter hm hn x)^2) := by
  have h := (nonlinear_square_integrable hm hn
    (mul_nonneg C.sigma_positive.le G.coupling_positive.le)).div_const (C.sigma^2)
  simpa only [calibrationFilter,div_pow] using h

/--
Integrability of the displayed function: `Integrable (fun x => groundParameter hm hn*m
x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn x)^2)`.

Use: `chebyshev2.Calibration.Data.calibrationState_derivative_integrable` uses this
integrability result to establish integrability of the displayed function: `Integrable (fun x
=> (G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.Data.calibrationFilter_integrable`,
`chebyshev2.Calibration.Data.calibrationFilter_square_integrable` with the arguments shown
in the proof.
-/
theorem calibrationFilter_derivative_integrable : Integrable (fun x =>
    groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn x)^2) :=
  ((hm.const_mul _).sub ((C.calibrationFilter_integrable G).const_mul 2)).sub
    ((C.calibrationFilter_square_integrable G).const_mul C.sigma)

/--
Integrability of the displayed function: `Integrable (fun x => (G.q
x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)`.

Use: `chebyshev2.Calibration.Data.J_composition_integrable` uses this integrability result
to establish integrability of the displayed function: `Integrable (fun x => C.Jprime
(C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn
x)^2-2*C.calibrationState G x))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coordinate_integrability`,
`chebyshev2.Calibration.Data.calibrationFilter_derivative_integrable` with the arguments
shown in the proof.
-/
theorem calibrationState_derivative_integrable : Integrable (fun x =>
    (G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x) := by
  apply (G.coordinate_integrability.2.sub (C.calibrationFilter_derivative_integrable G)).congr
  exact Eventually.of_forall (fun x => by
    change (groundParameter hm hn*m x-G.q x*(2-G.q x))-
      (groundParameter hm hn*m x-2*C.calibrationFilter hm hn x-C.sigma*(C.calibrationFilter hm hn x)^2)=_
    unfold calibrationState
    ring)

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(C.calibrationFilter hm hn) atBot (𝓝 0) ∧ Tendsto (C.calibrationFilter hm hn) atTop (𝓝 0)`.

Use: `chebyshev2.Calibration.Data.calibrationState_limits` uses this limit to establish
convergence along the specified source filter to the specified limit: `Tendsto
(C.calibrationState G) atBot (𝓝 0) ∧ Tendsto (C.calibrationState G) atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Filters.nonlinear_limits`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem calibrationFilter_limits : Tendsto (C.calibrationFilter hm hn) atBot (𝓝 0) ∧
    Tendsto (C.calibrationFilter hm hn) atTop (𝓝 0) := by
  have h := nonlinear_limits hm hn (mul_nonneg C.sigma_positive.le G.coupling_positive.le)
  change Tendsto (fun x => nonlinear (C.sigma*groundParameter hm hn) m x/C.sigma) atBot (𝓝 0) ∧
    Tendsto (fun x => nonlinear (C.sigma*groundParameter hm hn) m x/C.sigma) atTop (𝓝 0)
  exact ⟨by simpa only [zero_div] using h.1.div_const C.sigma,
    by simpa only [zero_div] using h.2.div_const C.sigma⟩

/--
Convergence along the specified source filter to the specified limit: `Tendsto
(C.calibrationState G) atBot (𝓝 0) ∧ Tendsto (C.calibrationState G) atTop (𝓝 2)`.

Use: `chebyshev2.Calibration.Data.J_composition_mass` uses this limit to establish exact
identity `(∫ x, C.Jprime (C.calibrationState G x)* ((G.q x)^2+C.sigma*(C.calibrationFilter hm
hn x)^2-2*C.calibrationState G x))=C.J 2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates
`chebyshev2.GroundState.GroundWitness.coordinate_limits`,
`chebyshev2.Calibration.Data.calibrationFilter_limits` with the arguments shown in the
proof.
-/
theorem calibrationState_limits : Tendsto (C.calibrationState G) atBot (𝓝 0) ∧
    Tendsto (C.calibrationState G) atTop (𝓝 2) := by
  change Tendsto (fun x => G.q x-C.calibrationFilter hm hn x) atBot (𝓝 0) ∧
    Tendsto (fun x => G.q x-C.calibrationFilter hm hn x) atTop (𝓝 2)
  exact ⟨by simpa only [sub_zero] using G.coordinate_limits.1.sub (C.calibrationFilter_limits G).1,
    by simpa only [sub_zero] using G.coordinate_limits.2.sub (C.calibrationFilter_limits G).2⟩

/--
Equation (14), with the actual Fredholm logarithm at the moving scale.

The precise assertion is `(∫ x, (C.calibrationFilter hm hn x)^2)= groundParameter hm hn*(∫ x, m
x)/C.sigma- 2/C.sigma^2*chebyshev2.Continuum.logDeterminant
(chebyshev2.Continuum.kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn)`.

Use: `chebyshev2.Calibration.Data.base_identity` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem calibrationFilter_square_mass : (∫ x, (C.calibrationFilter hm hn x)^2)=
    groundParameter hm hn*(∫ x, m x)/C.sigma-
      2/C.sigma^2*chebyshev2.Continuum.logDeterminant (chebyshev2.Continuum.kernelEigenvalue hm hn)
        (C.sigma*groundParameter hm hn) := by
  simp only [calibrationFilter,div_pow,integral_div,
    nonlinear_square_mass hm hn (mul_nonneg C.sigma_positive.le G.coupling_positive.le)]
  field_simp [C.sigma_positive.ne']

omit G in
/--
Exact identity `(q-h)^2+C.Jprime h*(q^2+C.sigma*(q-h)^2-2*h)=C.F q h`.

Use: `chebyshev2.Calibration.Data.calibration_identity_ae` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, (C.calibrationFilter hm
hn x)^2+deriv (fun x => C.J (C.calibrationState G x)) x= C.F (G.q x) (C.calibrationState G x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.denominator_positive` with
the arguments shown in the proof.
-/
theorem calibration_identity (q h : ℝ) :
    (q-h)^2+C.Jprime h*(q^2+C.sigma*(q-h)^2-2*h)=C.F q h := by
  unfold Jprime F
  apply (eq_div_iff (C.denominator_positive h).ne').2
  rw [add_mul,div_mul_eq_mul_div,div_mul_cancel₀ _ (C.denominator_positive h).ne']
  ring

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, (C.calibrationFilter hm
hn x)^2+deriv (fun x => C.J (C.calibrationState G x)) x= C.F (G.q x) (C.calibrationState G x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem calibration_identity_ae : ∀ᵐ x,
    (C.calibrationFilter hm hn x)^2+deriv (fun x => C.J (C.calibrationState G x)) x=
      C.F (G.q x) (C.calibrationState G x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [C.calibrationState_derivative G] with x hx
  have h := (C.J_derivative (C.calibrationState G x)).comp x hx
  change HasDerivAt (fun x => C.J (C.calibrationState G x))
    (C.Jprime (C.calibrationState G x)*
      ((G.q x)^2+C.sigma*(C.calibrationFilter hm hn x)^2-2*C.calibrationState G x)) x at h
  rw [h.deriv]
  convert C.calibration_identity (G.q x) (C.calibrationState G x) using 1
  dsimp [calibrationState]
  ring

end Data
end
end chebyshev2.Calibration

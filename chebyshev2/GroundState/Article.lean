import chebyshev2.GroundState.CoordinateBounds
import chebyshev2.GroundState.Simplicity

/-!
Article: chebyshev2, Proposition 4.
The coordinate depends only on m: every other positive classical ground solution gives the same
quotient, at every point.
Use: `chebyshev2.GroundState.GroundWitness.coordinate_integrability` feeds
`chebyshev2.Calibration.Data.amplitude_cube_integrable` (amplitude cube integrable).
Proof chain: `chebyshev2.Residual.statePotential_null` — chebyshev2, Theorem 3.5; Pointwise
cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.GroundState
noncomputable section
open chebyshev2.Continuum chebyshev2.Sobolev Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

/--
Minimal proved ground-state data; every further assertion of Theorem 3.1 is derived below.
`ground_state` constructs these data for the article's full class of nonnegative nonzero
integrable densities.

Use: `chebyshev2.GroundState.GroundWitness.d` uses this record of data and proof
obligations in the displayed construction of `d`. Its inputs and component formulas are fixed
by that definition.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.
-/
structure GroundWitness {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) where
  /-- Ground-state vector in the actual Sobolev Hilbert space. -/
  u : H1
  /-- Riccati data at the density's ground parameter. -/
  R : RiccatiData m (groundParameter hm hn)
  /-- The canonical representative of the ground-state vector is strictly positive everywhere. -/
  positive : ∀ x, 0 < H1.rep u x
  /-- Its derivative is the Riccati logarithmic derivative times the representative. -/
  derivative : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x
  /-- The ground-state vector is an eigenvector of the actual density operator at its leading kernel eigenvalue. -/
  eigen : densityOperator m u=kernelEigenvalue hm hn 0 • u
  /-- The density has positive total mass, excluding the zero-density degeneracy. -/
  mass_positive : 0 < ∫ x, m x

/--
The stated quantitative bound `0 < ∫ x, m x`.

Use: `chebyshev2.GroundState.ground_state` uses this bound to establish the precise
assertion is `Nonempty (GroundWitness hm hn)`.

Article: chebyshev2, Theorem 3.1 via `chebyshev2.GroundState.ground_state`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem density_mass_positive {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hne : ¬ m =ᵐ[volume] 0) : 0 < ∫ x, m x := by
  have hp : 0 ≤ ∫ x, m x := integral_nonneg (fun x => hn x)
  apply lt_of_le_of_ne hp
  intro hz
  exact hne ((integral_eq_zero_iff_of_nonneg hn hm).mp hz.symm)

/--
Theorem 3.1: construction from the literal nonzero-L1 hypothesis.

The precise assertion is `Nonempty (GroundWitness hm hn)`.

Use: `chebyshev2.Calibration.Data.one_determinant_lower_bound` uses this assertion to
establish the stated quantitative bound `ENNReal.ofReal (C.base (groundParameter hm hn)
(logDeterminant (kernelEigenvalue hm hn) (C.sigma*groundParameter hm hn))) ≤ ∫⁻ x,
ENNReal.ofReal (m x^(3/2:ℝ))`.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev2.GroundState.exists_unique_ground`,
`chebyshev2.GroundState.density_mass_positive` with the arguments shown in the proof.
-/
theorem ground_state {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hne : ¬ m =ᵐ[volume] 0) : Nonempty (GroundWitness hm hn) := by
  obtain ⟨u,R,hpos,hdu,he,_,_,_⟩ := exists_unique_ground hm hn (density_mass_positive hm hn hne)
  exact ⟨⟨u,R,hpos,hdu,he,density_mass_positive hm hn hne⟩⟩

namespace GroundWitness
variable {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x, 0 ≤ m x} (G : GroundWitness hm hn)
include G

/--
Defines `d` of type `ℝ` by `G.R.a x*H1.rep G.u x`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_unique` uses this definition to
establish exact identity `1-e x/H1.rep v x=G.q x`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.
-/
def d (x : ℝ) : ℝ := G.R.a x*H1.rep G.u x
/--
Defines `q` of type `ℝ → ℝ` by `G.R.q`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_eq` uses this definition to establish
exact identity `G.q x=1-G.d x/H1.rep G.u x`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.
-/
def q : ℝ → ℝ := G.R.q

/--
The stated quantitative bound `0 < groundParameter hm hn`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_limits` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto G.q atBot (𝓝 0)
∧ Tendsto G.q atTop (𝓝 2)`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.coordinate_limits`.

Proof: Use the identities/estimates `chebyshev2.GroundState.groundParameter_positive` with
the arguments shown in the proof.
-/
theorem coupling_positive : 0 < groundParameter hm hn := groundParameter_positive hm hn G.mass_positive
/--
Smoothness to the stated order: `ContDiff ℝ 1 (H1.rep G.u)`.

Use: `chebyshev2.GroundState.GroundWitness.d_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval G.d a b`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.ground_contDiff`
with the arguments shown in the proof.
-/
theorem c1 : ContDiff ℝ 1 (H1.rep G.u) := G.R.ground_contDiff G.derivative
/--
The precise assertion is `MemLp G.d 2 volume`.

Use: `chebyshev2.Comparison.reflectedGround_regular` uses this assertion to establish the
stated quantitative bound `SobolevRegular (fun x => H1.rep G.u (-x)) (fun x => -G.d (-x)) where
value_memLp`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.weighted_memLp`
with the arguments shown in the proof.
-/
theorem d_memLp : MemLp G.d 2 volume := G.R.weighted_memLp G.u

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval G.d a b`.

Use: `chebyshev2.Comparison.groundSlope_hasDerivAt` uses this assertion to establish the
actual derivative at the stated point: `HasDerivAt G.d ((1-groundParameter hm hn*m x)*H1.rep
G.u x) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.c1` with the
arguments shown in the proof.
-/
theorem d_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval G.d a b := by
  have hu : AbsolutelyContinuousOnInterval (H1.rep G.u) a b := G.c1.contDiffOn.absolutelyContinuousOnInterval
  apply ((G.R.locally_ac a b).mul hu).congr
  intro x _
  rfl

/--
The stated quantitative bound `|G.d x| ≤ H1.rep G.u x`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem d_abs_le (x : ℝ) : |G.d x| ≤ H1.rep G.u x := by
  change |G.R.a x*H1.rep G.u x| ≤ H1.rep G.u x
  rw [abs_mul,abs_of_pos (G.positive x)]
  exact mul_le_of_le_one_left (G.positive x).le (G.R.bound x)

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt G.d
((1-groundParameter hm hn*m x)*H1.rep G.u x) x`.

Use: `chebyshev2.Comparison.groundSlope_hasDerivAt` uses this assertion to establish the
actual derivative at the stated point: `HasDerivAt G.d ((1-groundParameter hm hn*m x)*H1.rep
G.u x) x`.

Article: chebyshev2, Theorem 3.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem ode : ∀ᵐ x, HasDerivAt G.d ((1-groundParameter hm hn*m x)*H1.rep G.u x) x := by
  filter_upwards [G.R.derivative_ae] with x hx
  have hd := hx.mul (G.derivative x)
  change HasDerivAt G.d
    ((1-groundParameter hm hn*m x-G.R.a x^2)*H1.rep G.u x+
      G.R.a x*(G.R.a x*H1.rep G.u x)) x at hd
  convert hd using 1
  ring

/--
Exact identity `G.d x/H1.rep G.u x=G.R.a x`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_eq` rewrites with this identity to
establish exact identity `G.q x=1-G.d x/H1.rep G.u x`.

Article: chebyshev2, Theorem 3.1 via
`chebyshev2.GroundState.GroundWitness.square_identity`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem quotient (x : ℝ) : G.d x/H1.rep G.u x=G.R.a x :=
  mul_div_cancel_right₀ _ (ne_of_gt (G.positive x))

/--
Exact identity `G.q x=1-G.d x/H1.rep G.u x`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_unique` rewrites with this identity
to establish the identity `1-e x/H1.rep v x=G.q x`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.quotient` with
the arguments shown in the proof.
-/
theorem coordinate_eq (x : ℝ) : G.q x=1-G.d x/H1.rep G.u x := by rw [G.quotient]; rfl

/--
The precise assertion is `‖f‖^2-groundParameter hm hn*(∫ x, m x*H1.rep f x^2)= ∫ x, (H1.slope f
x-(G.d x/H1.rep G.u x)*H1.rep f x)^2`.

Use: `chebyshev2.HalfLine.ground_strict_dirichlet` rewrites with this identity to establish
the stated quantitative bound `groundParameter hm hn*(∫ t, m t*(H1.rep u t)^2) < ‖u‖^2`.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.quotient`,
`chebyshev2.GroundState.RiccatiData.square_identity` with the arguments shown in the proof.
-/
theorem square_identity (f : H1) :
    ‖f‖^2-groundParameter hm hn*(∫ x, m x*H1.rep f x^2)=
      ∫ x, (H1.slope f x-(G.d x/H1.rep G.u x)*H1.rep f x)^2 := by
  simp_rw [G.quotient]
  exact (G.R.square_identity hm f).symm

/--
Equivalence of the displayed criteria: `(∫ x, (H1.slope f x-(G.d x/H1.rep G.u x)*H1.rep f
x)^2)=0 ↔ ∃ r : ℝ, f=r • G.u`.

Use: `chebyshev2.HalfLine.ground_strict_dirichlet` uses this identity to establish the
stated quantitative bound `groundParameter hm hn*(∫ t, m t*(H1.rep u t)^2) < ‖u‖^2`.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.quotient`,
`chebyshev2.GroundState.RiccatiData.residual_integral_eq_zero_iff_smul` with the arguments
shown in the proof.
-/
theorem square_eq_zero_iff (f : H1) :
    (∫ x, (H1.slope f x-(G.d x/H1.rep G.u x)*H1.rep f x)^2)=0 ↔ ∃ r : ℝ, f=r • G.u := by
  simp_rw [G.quotient]
  exact G.R.residual_integral_eq_zero_iff_smul G.positive G.derivative f

/--
Constructs witnesses with the exact properties `∃ r : ℝ, v=r • G.u`.

Use: `chebyshev2.GroundState.GroundWitness.positive_multiple` uses this identity to
establish constructs witnesses with the exact properties `∃ r : ℝ, 0 < r ∧ v=r • G.u`.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates
`chebyshev2.GroundState.RiccatiData.residual_integral_eq_zero_iff_smul`,
`chebyshev2.GroundState.RiccatiData.square_identity`,
`chebyshev2.GroundState.ode_energy` with the arguments shown in the proof.
-/
theorem unique_solution (v : H1) {e : ℝ → ℝ}
    (hv : ∀ᵐ x, HasDerivAt (H1.rep v) (e x) x)
    (he : ∀ a b, AbsolutelyContinuousOnInterval e a b)
    (hode : ∀ᵐ x, HasDerivAt e ((1-groundParameter hm hn*m x)*H1.rep v x) x) :
    ∃ r : ℝ, v=r • G.u := by
  apply (G.R.residual_integral_eq_zero_iff_smul G.positive G.derivative v).mp
  rw [G.R.square_identity hm,ode_energy hm _ v hv he hode,sub_self]

/--
Constructs witnesses with the exact properties `∃ r : ℝ, 0 < r ∧ v=r • G.u`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_unique` uses this identity to
establish exact identity `1-e x/H1.rep v x=G.q x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.GroundWitness.unique_solution`,
`chebyshev2.Sobolev.H1.rep_smul` with the arguments shown in the proof.
-/
theorem positive_multiple (v : H1) (hpos : ∀ x, 0 < H1.rep v x) {e : ℝ → ℝ}
    (hv : ∀ᵐ x, HasDerivAt (H1.rep v) (e x) x)
    (he : ∀ a b, AbsolutelyContinuousOnInterval e a b)
    (hode : ∀ᵐ x, HasDerivAt e ((1-groundParameter hm hn*m x)*H1.rep v x) x) :
    ∃ r : ℝ, 0 < r ∧ v=r • G.u := by
  -- Use the identities/estimates `chebyshev2.GroundState.GroundWitness.unique_solution`,
  -- `chebyshev2.Sobolev.H1.rep_smul` with the arguments shown in the proof.
  obtain ⟨r,hr⟩ := G.unique_solution v hv he hode
  refine ⟨r,?_,hr⟩
  have hp := hpos 0
  rw [hr,H1.rep_smul] at hp
  exact (mul_pos_iff_of_pos_right (G.positive 0)).mp hp

/--
Convergence along the specified source filter to the specified limit: `Tendsto G.q atBot (𝓝 0)
∧ Tendsto G.q atTop (𝓝 2)`.

Use: `chebyshev2.GroundState.GroundWitness.coordinate_support` uses this limit to establish
exact identity `(∀ x ≤ a, G.q x=0) ∧ (∀ x, b ≤ x → G.q x=2)`.

Article: chebyshev2, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_endpoint_limits`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem coordinate_limits : Tendsto G.q atBot (𝓝 0) ∧ Tendsto G.q atTop (𝓝 2) :=
  G.R.q_endpoint_limits hm hn G.coupling_positive.le G.positive G.derivative

/--
Membership in the specified domain/enclosure: `G.q x ∈ Icc (0:ℝ) 2`.

Use: `chebyshev2.Calibration.Data.Gamma_integrable` rewrites with this assertion to
establish integrability of the displayed function: `Integrable (fun x => C.Gamma (G.q x))`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_mem` with the
arguments shown in the proof.
-/
theorem coordinate_mem (x : ℝ) : G.q x ∈ Icc (0:ℝ) 2 := G.R.q_mem x
/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval G.q a b`.

Use: `chebyshev2.Calibration.Data.V_composition_mass` uses this assertion to establish
exact identity `(∫ x, C.Vprime (groundParameter hm hn) (G.q x)* (groundParameter hm hn*m x-Q
(G.q x)))=C.V (groundParameter hm hn) 2`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_locallyAC` with
the arguments shown in the proof.
-/
theorem coordinate_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval G.q a b := G.R.q_locallyAC a b
/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt G.q
(groundParameter hm hn*m x-G.q x*(2-G.q x)) x`.

Use: `chebyshev2.Calibration.Data.V_composition_derivative` uses this assertion to
establish establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (fun
x => C.V (groundParameter hm hn) (G.q x)) (C.Vprime (groundParameter hm hn) (G.q
x)*(groundParameter hm hn*m x-Q (G.q x))) x`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_derivative_ae`
with the arguments shown in the proof.
-/
theorem coordinate_derivative : ∀ᵐ x, HasDerivAt G.q
    (groundParameter hm hn*m x-G.q x*(2-G.q x)) x := G.R.q_derivative_ae

/--
Exact identity `(∀ x ≤ a, G.q x=0) ∧ (∀ x, b ≤ x → G.q x=2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_zero_left`,
`chebyshev2.GroundState.GroundWitness.coordinate_limits`,
`chebyshev2.GroundState.RiccatiData.q_two_right` with the arguments shown in the proof.
-/
theorem coordinate_support {a b : ℝ}
    (hl : ∀ x < a, m x=0) (hr : ∀ x, b < x → m x=0) :
    (∀ x ≤ a, G.q x=0) ∧ (∀ x, b ≤ x → G.q x=2) :=
  ⟨fun _ hx => G.R.q_zero_left hl G.coordinate_limits.1 hx,
    fun _ hx => G.R.q_two_right hr G.coordinate_limits.2 hx⟩

/--
The displayed Lipschitz bound: `LipschitzWith (Real.toNNReal (groundParameter hm hn*B+1)) G.q`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.q_lipschitz`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem coordinate_lipschitz {B : ℝ} (hB : 0 ≤ B) (hmb : ∀ x, m x ≤ B) :
    LipschitzWith (Real.toNNReal (groundParameter hm hn*B+1)) G.q :=
  G.R.q_lipschitz G.coupling_positive.le hB hn hmb

/--
The coordinate depends only on m: every other positive classical ground solution gives the same
quotient, at every point.

Exact identity `1-e x/H1.rep v x=G.q x`.

Use: `chebyshev2.Comparison.groundCoordinate_reflection` uses this identity to establish
exact identity `Gr.q x=2-G.q (-x)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coordinate_unique (v : H1) (hpos : ∀ x, 0 < H1.rep v x) {e : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt (H1.rep v) (e x) x)
    (he : ∀ a b, AbsolutelyContinuousOnInterval e a b)
    (hode : ∀ᵐ x, HasDerivAt e ((1-groundParameter hm hn*m x)*H1.rep v x) x) (x : ℝ) :
    1-e x/H1.rep v x=G.q x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨r,hr,hrv⟩ := G.positive_multiple v hpos (Filter.Eventually.of_forall hv) he hode
  have hd := (G.derivative x).const_mul r
  have hfun : (fun x => r*H1.rep G.u x)=H1.rep v := by rw [hrv,H1.rep_smul]
  rw [hfun] at hd
  have hdx : e x=r*G.d x := (hv x).unique hd
  rw [hdx,hrv,H1.rep_smul,G.coordinate_eq]
  change 1-(r*G.d x)/(r*H1.rep G.u x)=1-G.d x/H1.rep G.u x
  field_simp [ne_of_gt hr,ne_of_gt (G.positive x)]

/--
Exact identity `(∫ x, G.q x*(2-G.q x))=groundParameter hm hn*(∫ x, m x)-2`.

Use: `chebyshev2.Calibration.Data.flowResidual_integral` uses this identity to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.Q_mass`,
`chebyshev2.GroundState.GroundWitness.coupling_positive` with the arguments shown in the
proof.
-/
theorem coordinate_mass : (∫ x, G.q x*(2-G.q x))=groundParameter hm hn*(∫ x, m x)-2 :=
  G.R.Q_mass hm hn G.coupling_positive.le G.positive G.derivative

/--
Integrability of the displayed function: `Integrable (fun x => G.q x*(2-G.q x)) ∧ Integrable
(fun x => groundParameter hm hn*m x-G.q x*(2-G.q x))`.

Use: `chebyshev2.Calibration.Data.Gamma_integrable` uses this integrability result to
establish integrability of the displayed function: `Integrable (fun x => C.Gamma (G.q x))`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.statePotential_null`.

Proof: Use the identities/estimates `chebyshev2.GroundState.RiccatiData.Q_integrable`,
`chebyshev2.GroundState.GroundWitness.coupling_positive`,
`chebyshev2.GroundState.RiccatiData.q_derivative_integrable` with the arguments shown in
the proof.
-/
theorem coordinate_integrability : Integrable (fun x => G.q x*(2-G.q x)) ∧
    Integrable (fun x => groundParameter hm hn*m x-G.q x*(2-G.q x)) :=
  ⟨G.R.Q_integrable hm hn G.coupling_positive.le,G.R.q_derivative_integrable hm hn G.coupling_positive.le⟩

/--
Exact identity `Module.finrank ℝ (Module.End.eigenspace (kernelOperator hm hn).toLinearMap
(kernelEigenvalue hm hn 0))=1`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Use the identities/estimates `chebyshev2.GroundState.kernel_ground_simple` with the
arguments shown in the proof.
-/
theorem simple : Module.finrank ℝ
    (Module.End.eigenspace (kernelOperator hm hn).toLinearMap (kernelEigenvalue hm hn 0))=1 :=
  kernel_ground_simple hm hn G.mass_positive

/--
Equivalence of the displayed criteria: `(∀ f : H1, c*(∫ x, m x*H1.rep f x^2) ≤ ‖f‖^2) ↔ c ≤
groundParameter hm hn`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 4.

Proof: Use the identities/estimates `chebyshev2.GroundState.groundParameter_variational`
with the arguments shown in the proof.
-/
theorem variational (c : ℝ) :
    (∀ f : H1, c*(∫ x, m x*H1.rep f x^2) ≤ ‖f‖^2) ↔ c ≤ groundParameter hm hn :=
  groundParameter_variational hm hn G.mass_positive c

end GroundWitness
end
end chebyshev2.GroundState

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Article: 2610.05164v2, Theorem 3.6.
The rational coordinates of Appendix C.2.
Use: `«2610.05164v2».StateRegion.Scales.theta_bounds` feeds
`«2610.05164v2».StateRegion.Scales.normalized_bounds` (normalized bounds).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».StateRegion
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/--
Positive ground/observation parameters with a strictly positive observation gap. These sign
hypotheses make the state-coordinate transformations nondegenerate.

Use: `«2610.05164v2».StateRegion.Scales.D_lower` uses this record of data and proof obligations
to prove the bound `S.k₀ ≤ S.D w`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
structure Scales where
  /-- Positive ground-parameter scale. -/
  k : ℝ
  /-- Positive first observation parameter. -/
  a : ℝ
  /-- Positive separation between the two observation scales. -/
  gap : ℝ
  /-- Strict positivity needed for ground-parameter normalization. -/
  k_pos : 0 < k
  /-- Strict positivity of the first observation scale. -/
  a_pos : 0 < a
  /-- Strict separation of the observation scales. -/
  gap_pos : 0 < gap

namespace Scales
variable (S : Scales)

/--
Defines `b` of type `ℝ` by `S.a + S.gap`.

Use: `«2610.05164v2».StateRegion.Scales.f_change` uses this definition to establish exact
identity `S.f (S.change z)=S.response S.b z`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def b : ℝ := S.a + S.gap
/--
Defines `k₀` of type `ℝ` by `S.k + S.a`.

Use: `«2610.05164v2».StateRegion.Scales.D_lower` uses this definition to establish the stated
quantitative bound `S.k₀ ≤ S.D w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def k₀ : ℝ := S.k + S.a
/--
Defines `k₁` of type `ℝ` by `S.k + S.a + S.gap`.

Use: `«2610.05164v2».StateRegion.Scales.D` uses this definition in the displayed construction
of `D`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def k₁ : ℝ := S.k + S.a + S.gap
/--
Defines `D` of type `ℝ` by `S.k₁ - S.gap * w`.

Use: `«2610.05164v2».StateRegion.Scales.D_lower` uses this definition to establish the stated
quantitative bound `S.k₀ ≤ S.D w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def D (w : ℝ) : ℝ := S.k₁ - S.gap * w
/--
Defines `E` of type `ℝ` by `S.k + S.a * w`.

Use: `«2610.05164v2».StateRegion.Scales.E_lower` uses this definition to establish the stated
quantitative bound `S.k ≤ S.E w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def E (w : ℝ) : ℝ := S.k + S.a * w
/--
Defines `f` of type `ℝ` by `S.k₀ * w / S.D w`.

Use: `«2610.05164v2».StateRegion.Scales.V` uses this definition in the displayed construction
of `V`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def f (w : ℝ) : ℝ := S.k₀ * w / S.D w
/--
Defines `g` of type `ℝ` by `S.k₀ * w / S.E w`.

Use: `«2610.05164v2».StateRegion.Scales.g_mem` rewrites with this definition to establish
membership in the specified domain/enclosure: `S.g w ∈ Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def g (w : ℝ) : ℝ := S.k₀ * w / S.E w
/--
Defines `change` of type `ℝ` by `S.k * (1-z) / S.E z`.

Use: `«2610.05164v2».StateRegion.Scales.change_involution` uses this definition to establish
exact identity `S.change (S.change z) = z`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def change (z : ℝ) : ℝ := S.k * (1-z) / S.E z

/--
The stated quantitative bound `0 < S.k₀`.

Use: `«2610.05164v2».StateRegion.Scales.D_pos` uses this bound to establish the stated
quantitative bound `0 < S.D w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem k₀_pos : 0 < S.k₀ := add_pos S.k_pos S.a_pos
/--
The stated quantitative bound `0 < S.k₁`.

Use: `«2610.05164v2».StateRegion.Scales.yPlus_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ S.yPlus u t ∧ S.yPlus u t ≤ u`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos` with the
arguments shown in the proof.
-/
theorem k₁_pos : 0 < S.k₁ := add_pos S.k₀_pos S.gap_pos
/--
The stated quantitative bound `S.k₀ ≤ S.D w`.

Use: `«2610.05164v2».StateRegion.Scales.D_pos` uses this bound to establish the stated
quantitative bound `0 < S.D w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem D_lower {w : ℝ} (hw : w ≤ 1) : S.k₀ ≤ S.D w := by
  dsimp [D, k₀, k₁]
  nlinarith [S.gap_pos]
/--
The stated quantitative bound `0 < S.D w`.

Use: `«2610.05164v2».StateRegion.Scales.f_le_self` rewrites with this bound to establish the
stated quantitative bound `S.f w ≤ w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.D_lower` with the arguments shown in the proof.
-/
theorem D_pos {w : ℝ} (hw : w ≤ 1) : 0 < S.D w := S.k₀_pos.trans_le (S.D_lower hw)
/--
The stated quantitative bound `S.k ≤ S.E w`.

Use: `«2610.05164v2».StateRegion.Scales.E_pos` uses this bound to establish the stated
quantitative bound `0 < S.E w`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem E_lower {w : ℝ} (hw : 0 ≤ w) : S.k ≤ S.E w := by
  dsimp [E]
  exact le_add_of_nonneg_right (mul_nonneg S.a_pos.le hw)
/--
The stated quantitative bound `0 < S.E w`.

Use: `«2610.05164v2».StateRegion.Scales.change_involution` uses this bound to establish exact
identity `S.change (S.change z) = z`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.E_lower` with the
arguments shown in the proof.
-/
theorem E_pos {w : ℝ} (hw : 0 ≤ w) : 0 < S.E w := S.k_pos.trans_le (S.E_lower hw)

/--
Exact identity `S.f 0 = 0`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaPlus` rewrites with this identity to
establish the precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaPlus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem f_zero : S.f 0 = 0 := by simp [f]
/--
Exact identity `S.f 1 = 1`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaMinus` rewrites with this identity to
establish the precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos` with the
arguments shown in the proof.
-/
@[simp] theorem f_one : S.f 1 = 1 := by
  dsimp [f, D, k₁]
  rw [mul_one, mul_one, add_sub_cancel_right]
  exact div_self S.k₀_pos.ne'
/--
Exact identity `S.g 0 = 0`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaPlus` rewrites with this identity to
establish the precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaPlus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem g_zero : S.g 0 = 0 := by simp [g]
/--
Exact identity `S.g 1 = 1`.

Use: `«2610.05164v2».StateRegion.Scales.attain_thetaMinus` rewrites with this identity to
establish the precise assertion is `Nonempty (MomentWitness S u (S.V u t) (S.thetaMinus u t))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos` with the
arguments shown in the proof.
-/
@[simp] theorem g_one : S.g 1 = 1 := by
  change S.k₀ * 1 / (S.k + S.a * 1) = 1
  simpa only [mul_one, k₀] using div_self S.k₀_pos.ne'

/--
The stated quantitative bound `0 ≤ S.f w`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this bound to
establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.D_pos` with the arguments shown in the proof.
-/
theorem f_nonneg {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : 0 ≤ S.f w :=
  div_nonneg (mul_nonneg S.k₀_pos.le hw.1) (S.D_pos hw.2).le
/--
The stated quantitative bound `S.f w ≤ w`.

Use: `«2610.05164v2».StateRegion.Scales.V_bounds` uses this bound to establish the stated
quantitative bound `S.f u ≤ S.V u t ∧ S.V u t ≤ u`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.D_pos`,
`«2610.05164v2».StateRegion.Scales.D_lower` with the arguments shown in the proof.
-/
theorem f_le_self {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : S.f w ≤ w := by
  rw [f, div_le_iff₀ (S.D_pos hw.2)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (S.D_lower hw.2) hw.1
/--
Membership in the specified domain/enclosure: `S.g w ∈ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».StateRegion.Scales.g_integrable` rewrites with this assertion to establish
integrability of the displayed function: `Integrable S.g μ`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.E_pos` with the arguments shown in the proof.
-/
theorem g_mem {w : ℝ} (hw : w ∈ Icc (0:ℝ) 1) : S.g w ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (mul_nonneg S.k₀_pos.le hw.1) (S.E_pos hw.1).le
  · rw [g, div_le_iff₀ (S.E_pos hw.1)]
    dsimp [k₀, E]
    nlinarith [S.k_pos, hw.2]

/--
Membership in the specified domain/enclosure: `S.change z ∈ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».StateRegion.Scales.change_involution` uses this assertion to establish
exact identity `S.change (S.change z) = z`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.E_pos` with the
arguments shown in the proof.
-/
theorem change_mem {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : S.change z ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (mul_nonneg S.k_pos.le (sub_nonneg.mpr hz.2)) (S.E_pos hz.1).le
  · rw [change, div_le_iff₀ (S.E_pos hz.1)]
    dsimp [E]
    nlinarith [S.a_pos, S.k_pos, hz.1]

/--
Exact identity `S.change (S.change z) = z`.

Use: `«2610.05164v2».StateRegion.Scales.g_change` rewrites with this identity to establish
exact identity `S.g (S.change z)=1-z`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem change_involution {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    S.change (S.change z) = z := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h₁ := (S.E_pos hz.1).ne'
  have h₂ := (S.E_pos (S.change_mem hz).1).ne'
  change S.k * (1-S.change z) / S.E (S.change z) = z
  rw [div_eq_iff h₂]
  dsimp [change, E]
  change S.k + S.a*z ≠ 0 at h₁
  have h₃ : S.k+z*S.a ≠ 0 := by simpa only [mul_comm] using h₁
  field_simp [h₁, h₃]
  ring

/--
Tangent remainder: a direct certificate for Jensen's inequality, also recording its exact
equality case.

Exact identity `S.f w - (S.f u + S.k₀*S.k₁/(S.D u)^2*(w-u)) = S.k₀*S.k₁*S.gap*(w-u)^2 / ((S.D
u)^2*S.D w)`.

Use: `«2610.05164v2».StateRegion.Scales.lower_boundary_ae` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᵐ w ∂μ, w=u`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem f_tangent_remainder {u w : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1) :
    S.f w - (S.f u + S.k₀*S.k₁/(S.D u)^2*(w-u)) =
      S.k₀*S.k₁*S.gap*(w-u)^2 / ((S.D u)^2*S.D w) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd := (S.D_pos hu.2).ne'
  have hw' := (S.D_pos hw.2).ne'
  dsimp [f]
  field_simp
  dsimp [D, k₀, k₁]
  ring

/--
Defines `V` of type `ℝ` by `(1-t)*S.f u+t*u`.

Use: `«2610.05164v2».StateRegion.Scales.V_bounds` uses this definition to establish the stated
quantitative bound `S.f u ≤ S.V u t ∧ S.V u t ≤ u`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def V (u t : ℝ) : ℝ := (1-t)*S.f u+t*u
/--
Defines `yPlus` of type `ℝ` by `S.k₁*u*(1-t)/(S.k₁-S.gap*u*t)`.

Use: `«2610.05164v2».StateRegion.Scales.thetaMinus` uses this definition in the displayed
construction of `thetaMinus`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def yPlus (u t : ℝ) : ℝ := S.k₁*u*(1-t)/(S.k₁-S.gap*u*t)
/--
Defines `yMinus` of type `ℝ` by `(S.k₀*u+S.k₁*t*(1-u))/(S.k₀+S.gap*t*(1-u))`.

Use: `«2610.05164v2».StateRegion.Scales.thetaPlus` uses this definition in the displayed
construction of `thetaPlus`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def yMinus (u t : ℝ) : ℝ :=
  (S.k₀*u+S.k₁*t*(1-u))/(S.k₀+S.gap*t*(1-u))
/--
Defines `thetaMinus` of type `ℝ` by `S.k*(1-u)/S.E (S.yPlus u t)`.

Use: `«2610.05164v2».StateRegion.Scales.theta_bounds` rewrites with this definition to
establish membership in the specified domain/enclosure: `S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧
S.thetaPlus u t ∈ Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def thetaMinus (u t : ℝ) : ℝ := S.k*(1-u)/S.E (S.yPlus u t)
/--
Defines `thetaPlus` of type `ℝ` by `1-S.k₀*u/S.E (S.yMinus u t)`.

Use: `«2610.05164v2».StateRegion.Scales.theta_bounds` uses this definition to establish
membership in the specified domain/enclosure: `S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧ S.thetaPlus u t
∈ Icc (0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def thetaPlus (u t : ℝ) : ℝ := 1-S.k₀*u/S.E (S.yMinus u t)

/--
The stated quantitative bound `S.k₀ ≤ S.k₁-S.gap*u*t`.

Use: `«2610.05164v2».StateRegion.Scales.yPlus_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ S.yPlus u t ∧ S.yPlus u t ≤ u`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem yPlus_den_lower {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) : S.k₀ ≤ S.k₁-S.gap*u*t := by
  have hut : u*t ≤ 1 := by nlinarith [hu.2, mul_nonneg hu.1 (sub_nonneg.mpr ht.2)]
  dsimp [k₀,k₁]
  nlinarith [S.gap_pos]
/--
The stated quantitative bound `S.k₀ ≤ S.k₀+S.gap*t*(1-u)`.

Use: `«2610.05164v2».StateRegion.Scales.yMinus_bounds` uses this bound to establish the stated
quantitative bound `u ≤ S.yMinus u t ∧ S.yMinus u t ≤ 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem yMinus_den_lower {u t : ℝ} (hu : u ≤ 1) (ht : 0 ≤ t) :
    S.k₀ ≤ S.k₀+S.gap*t*(1-u) :=
  le_add_of_nonneg_right (mul_nonneg (mul_nonneg S.gap_pos.le ht) (sub_nonneg.mpr hu))

/--
The stated quantitative bound `0 ≤ S.yPlus u t ∧ S.yPlus u t ≤ u`.

Use: `«2610.05164v2».StateRegion.Scales.theta_bounds` uses this bound to establish membership
in the specified domain/enclosure: `S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧ S.thetaPlus u t ∈ Icc
(0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yPlus_den_lower`, `«2610.05164v2».StateRegion.Scales.k₁_pos`
with the arguments shown in the proof.
-/
theorem yPlus_bounds {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ S.yPlus u t ∧ S.yPlus u t ≤ u := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
  -- `«2610.05164v2».StateRegion.Scales.yPlus_den_lower`,
  -- `«2610.05164v2».StateRegion.Scales.k₁_pos` with the arguments shown in the proof.
  have hd := S.k₀_pos.trans_le (S.yPlus_den_lower hu ht)
  constructor
  · exact div_nonneg (mul_nonneg (mul_nonneg S.k₁_pos.le hu.1) (sub_nonneg.mpr ht.2)) hd.le
  · rw [yPlus, div_le_iff₀ hd]
    have hd' := S.D_pos hu.2
    have hp := mul_nonneg (mul_nonneg hu.1 ht.1) hd'.le
    dsimp [D] at hp
    nlinarith

/--
The stated quantitative bound `u ≤ S.yMinus u t ∧ S.yMinus u t ≤ 1`.

Use: `«2610.05164v2».StateRegion.Scales.theta_bounds` uses this bound to establish membership
in the specified domain/enclosure: `S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧ S.thetaPlus u t ∈ Icc
(0:ℝ) 1`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
`«2610.05164v2».StateRegion.Scales.yMinus_den_lower`, `«2610.05164v2».StateRegion.Scales.D_pos`
with the arguments shown in the proof.
-/
theorem yMinus_bounds {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) : u ≤ S.yMinus u t ∧ S.yMinus u t ≤ 1 := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.k₀_pos`,
  -- `«2610.05164v2».StateRegion.Scales.yMinus_den_lower`,
  -- `«2610.05164v2».StateRegion.Scales.D_pos` with the arguments shown in the proof.
  have hd := S.k₀_pos.trans_le (S.yMinus_den_lower hu.2 ht.1)
  constructor
  · rw [yMinus, le_div_iff₀ hd]
    have hp := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr hu.2)) (S.D_pos hu.2).le
    dsimp [D] at hp
    nlinarith
  · rw [yMinus, div_le_iff₀ hd]
    have hp := mul_nonneg S.k₀_pos.le
      (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr ht.2))
    dsimp [k₁, k₀] at *
    nlinarith

/--
The stated quantitative bound `S.f u ≤ S.V u t ∧ S.V u t ≤ u`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this bound to
establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.f_le_self` with the
arguments shown in the proof.
-/
theorem V_bounds {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) : S.f u ≤ S.V u t ∧ S.V u t ≤ u := by
  have hf := S.f_le_self hu
  dsimp [V]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hf),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hf)]

/--
Membership in the specified domain/enclosure: `S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧ S.thetaPlus u t
∈ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.Data.faceCriterion_continuous` uses this assertion to
establish continuity of the displayed function: `Continuous (D.faceCriterion i)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yPlus_bounds`,
`«2610.05164v2».StateRegion.Scales.yMinus_bounds`, `«2610.05164v2».StateRegion.Scales.E_pos`
with the arguments shown in the proof.
-/
theorem theta_bounds {u t : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (ht : t ∈ Icc (0:ℝ) 1) :
    S.thetaMinus u t ∈ Icc (0:ℝ) 1 ∧ S.thetaPlus u t ∈ Icc (0:ℝ) 1 := by
  -- Use the identities/estimates `«2610.05164v2».StateRegion.Scales.yPlus_bounds`,
  -- `«2610.05164v2».StateRegion.Scales.yMinus_bounds`,
  -- `«2610.05164v2».StateRegion.Scales.E_pos` with the arguments shown in the proof.
  obtain ⟨hy0,hyu⟩ := S.yPlus_bounds hu ht
  obtain ⟨huy,hy1⟩ := S.yMinus_bounds hu ht
  have hm := S.E_pos hy0
  have hp := S.E_pos (hu.1.trans huy)
  refine ⟨⟨div_nonneg (mul_nonneg S.k_pos.le (sub_nonneg.mpr hu.2)) hm.le, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [thetaMinus, div_le_iff₀ hm]
    dsimp [E]
    nlinarith [S.k_pos, S.a_pos]
  · have h : S.k₀*u ≤ S.E (S.yMinus u t) := by
      dsimp [k₀,E]
      nlinarith [S.k_pos, S.a_pos]
    exact sub_nonneg.mpr ((div_le_one hp).mpr h)
  · exact sub_le_self _ (div_nonneg (mul_nonneg S.k₀_pos.le hu.1) hp.le)

end Scales
end
end «2610.05164v2».StateRegion

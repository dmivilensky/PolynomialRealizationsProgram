import chebyshev2.PrescribedSpeed.Coordinate
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: chebyshev2, Theorem 3.2.
The globally clamped ground coordinate, equal to zero on the left and two on the right, as required
by Theorem 5.1.
Use: `chebyshev2.PrescribedSpeed.SpeedData.q_two_right` feeds
`chebyshev2.Calibration.ReferenceData.contactDerivative_positive` (contact Derivative positive).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_image` — chebyshev2, Theorem 3.2;
Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Exact identity `S.X '' Icc (0:ℝ) 2=Icc (S.X 0) (S.X 2)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.coordinateIso` uses this identity in the
displayed construction of `coordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.X_strictMono` with the arguments shown in the proof.
-/
theorem X_image : S.X '' Icc (0:ℝ) 2=Icc (S.X 0) (S.X 2) :=
  S.X_continuous.continuousOn.image_Icc_of_monotoneOn (by norm_num) S.X_strictMono.monotoneOn

/--
The actual coordinate order isomorphism, including both support endpoints.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_inverse` uses this definition to establish
exact identity `S.X (S.inverse x)=x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def coordinateIso : Icc (0:ℝ) 2 ≃o Icc (S.X 0) (S.X 2) :=
  (S.X_strictMono.orderIso S.X (Icc (0:ℝ) 2)).trans (Set.orderIsoOfEq _ _ S.X_image)

/--
Exact identity `(S.coordinateIso q : ℝ)=S.X q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.X_inverse` rewrites with this identity to
establish exact identity `S.X (S.inverse x)=x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coordinateIso_apply (q : Icc (0:ℝ) 2) : (S.coordinateIso q : ℝ)=S.X q := by simp [coordinateIso,StrictMonoOn.orderIso,Set.BijOn.equiv]

/--
Defines `inverse` of type `ℝ` by `(S.coordinateIso.symm x : ℝ)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.inverse_lipschitz` uses this definition to
establish the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal S.B) S.inverse`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def inverse (x : Icc (S.X 0) (S.X 2)) : ℝ := (S.coordinateIso.symm x : ℝ)

/--
Exact identity `S.X (S.inverse x)=x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.inverse_lipschitz` rewrites with this identity
to establish the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal S.B) S.inverse`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.coordinateIso_apply` with the arguments shown in the
proof.
-/
theorem X_inverse (x : Icc (S.X 0) (S.X 2)) : S.X (S.inverse x)=x := by
  have he := congrArg Subtype.val (S.coordinateIso.apply_symm_apply x)
  rw [S.coordinateIso_apply] at he
  exact he

/--
Exact identity `S.inverse (S.coordinateIso q)=q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.inverse_value` uses this identity to establish
exact identity `S.inverse ⟨S.X q,hx⟩=q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem inverse_X (q : Icc (0:ℝ) 2) : S.inverse (S.coordinateIso q)=q :=
  congrArg Subtype.val (S.coordinateIso.symm_apply_apply q)

/--
Exact identity `S.inverse ⟨S.X q,hx⟩=q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_X` uses this identity to establish exact
identity `S.q (S.X q)=q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.coordinateIso_apply`,
`chebyshev2.PrescribedSpeed.SpeedData.inverse_X` with the arguments shown in the proof.
-/
theorem inverse_value {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) (hx : S.X q ∈ Icc (S.X 0) (S.X 2)) :
    S.inverse ⟨S.X q,hx⟩=q := by
  have he : S.coordinateIso ⟨q,hq⟩=⟨S.X q,hx⟩ := Subtype.ext (S.coordinateIso_apply ⟨q,hq⟩)
  rw [← he]
  exact S.inverse_X ⟨q,hq⟩

/--
Exact inverse expansion bound for arbitrary measurable bounded speed.

The displayed Lipschitz bound: `LipschitzWith (Real.toNNReal S.B) S.inverse`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_lipschitz` uses this assertion to establish
the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal S.B) S.q`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_expansion`,
`chebyshev2.PrescribedSpeed.SpeedData.X_inverse` with the arguments shown in the proof.
-/
theorem inverse_lipschitz : LipschitzWith (Real.toNNReal S.B) S.inverse := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_expansion`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.X_inverse` with the arguments shown in the
  -- proof.
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have aux (x y : Icc (S.X 0) (S.X 2)) (hxy : x ≤ y) :
      dist (S.inverse x) (S.inverse y) ≤ (Real.toNNReal S.B : ℝ)*dist x y := by
    have hq : S.inverse x ≤ S.inverse y := S.coordinateIso.symm.monotone hxy
    have hb := S.X_expansion (S.coordinateIso.symm x).property (S.coordinateIso.symm y).property hq
    change (S.inverse y-S.inverse x)/S.B ≤ S.X (S.inverse y)-S.X (S.inverse x) at hb
    rw [S.X_inverse,S.X_inverse] at hb
    have he := (div_le_iff₀ S.bound_positive).mp hb
    have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hq),
      Subtype.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy'),
      Real.coe_toNNReal _ S.bound_positive.le]
    nlinarith
  rcases le_total x y with h | h
  · exact aux x y h
  · simpa only [dist_comm] using aux y x h

/--
The globally clamped ground coordinate, equal to zero on the left and two on the right, as
required by Theorem 5.1.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_X` rewrites with this definition to establish
exact identity `S.q (S.X q)=q`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.
-/
def q (x : ℝ) : ℝ := S.inverse (projIcc (S.X 0) (S.X 2) S.X_endpoint_order.le x)

/--
The displayed Lipschitz bound: `LipschitzWith (Real.toNNReal S.B) S.q`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.q_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.q a b`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.X_endpoint_order`,
`chebyshev2.PrescribedSpeed.SpeedData.inverse_lipschitz` with the arguments shown in the
proof.
-/
theorem q_lipschitz : LipschitzWith (Real.toNNReal S.B) S.q := by
  change LipschitzWith (Real.toNNReal S.B)
    (S.inverse ∘ projIcc (S.X 0) (S.X 2) S.X_endpoint_order.le)
  simpa only [mul_one] using S.inverse_lipschitz.comp (LipschitzWith.projIcc S.X_endpoint_order.le)

/--
Membership in the specified domain/enclosure: `S.q x ∈ Icc (0:ℝ) 2`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_reflection` uses this assertion to
establish exact identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.PrescribedSpeed.SpeedData.integral_q`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem q_mem (x : ℝ) : S.q x ∈ Icc (0:ℝ) 2 := (S.coordinateIso.symm _).property

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.q a b`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_derivative` uses this assertion to
establish the actual derivative at the stated point: `HasDerivAt (C.comparisonSpeed hκ).q
(κ*C.comparisonDensity hκ x-chebyshev2.Calibration.Q ((C.comparisonSpeed hκ).q x)) x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_lipschitz` with
the arguments shown in the proof.
-/
theorem q_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval S.q a b :=
  S.q_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval

/--
Exact identity `S.q (S.X q)=q`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_reflection` uses this identity to
establish exact identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_image`,
`chebyshev2.PrescribedSpeed.SpeedData.inverse_value` with the arguments shown in the proof.
-/
theorem q_X {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : S.q (S.X q)=q := by
  have hx : S.X q ∈ Icc (S.X 0) (S.X 2) := by
    rw [← S.X_image]
    exact mem_image_of_mem _ hq
  rw [SpeedData.q,projIcc_of_mem _ hx]
  exact S.inverse_value hq hx

/--
Exact identity `S.q x=0`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_reflection` rewrites with this
identity to establish the identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q
x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.inverse_value`
with the arguments shown in the proof.
-/
theorem q_zero_left {x : ℝ} (hx : x ≤ S.X 0) : S.q x=0 := by
  rw [SpeedData.q,projIcc_of_le_left _ hx]
  exact S.inverse_value (by norm_num) _

/--
Exact identity `S.q x=2`.

Use: `chebyshev2.Calibration.Data.comparisonCoordinate_reflection` rewrites with this
identity to establish the identity `(C.comparisonSpeed hκ).q (-x)=2-(C.comparisonSpeed hκ).q
x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.q_derivative_ae`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.inverse_value`
with the arguments shown in the proof.
-/
theorem q_two_right {x : ℝ} (hx : S.X 2 ≤ x) : S.q x=2 := by
  rw [SpeedData.q,projIcc_of_right_le _ hx]
  exact S.inverse_value (by norm_num) _

end SpeedData
end
end chebyshev2.PrescribedSpeed

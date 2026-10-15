import «2610.05164v2».GroundState.RegularGround
import «2610.05164v2».GroundState.SquareIdentity

/-!
Article: 2610.05164v2, Theorem 3.1.
The ground logarithmic derivative and equation (11) are constructed for every general L1 density;
the Riccati hypotheses are proved from its actual classical ground function, rather than supplied as
a certificate.
Use: `«2610.05164v2».GroundState.exists_ground_square_identity` feeds
`«2610.05164v2».GroundState.exists_unique_ground` (Simplicity on the actual Sobolev feature operator
and uniqueness of every H1 classical ODE solution, together with the complete square equality case).
Proof chain: `«2610.05164v2».GroundState.ground_state` — 2610.05164v2, Theorem 3.1; Sharp
ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Constructs `logDerivativeData` of type `RiccatiData m c` by the displayed record fields. Data
fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».GroundState.exists_ground_square_identity` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.
-/
def logDerivativeData {m : ℝ → ℝ} {c : ℝ} {u d : ℝ → ℝ}
    (hpos : ∀ x, 0 < u x) (huc : ContDiff ℝ 1 u)
    (hdu : ∀ x, HasDerivAt u (d x) x)
    (hdac : ∀ a b, AbsolutelyContinuousOnInterval d a b)
    (hbound : ∀ x, |d x| ≤ u x)
    (hode : ∀ᵐ x, HasDerivAt d ((1-c*m x)*u x) x) : RiccatiData m c where
  a x := d x/u x
  bound x := by
    rw [abs_div,abs_of_pos (hpos x)]
    exact (div_le_one (hpos x)).mpr (hbound x)
  locally_ac a b := by
    have hi : AbsolutelyContinuousOnInterval (fun x => (u x)⁻¹) a b :=
      ((huc.inv (fun x => ne_of_gt (hpos x))).contDiffOn :
        ContDiffOn ℝ 1 (fun x => (u x)⁻¹) (uIcc a b)).absolutelyContinuousOnInterval
    apply ((hdac a b).mul hi).congr
    intro x _
    exact (div_eq_mul_inv _ _).symm
  derivative_ae := by
    filter_upwards [hode] with x hx
    convert hx.div (hdu x) (ne_of_gt (hpos x)) using 1
    field_simp [ne_of_gt (hpos x)]

/--
The ground logarithmic derivative and equation (11) are constructed for every general L1
density; the Riccati hypotheses are proved from its actual classical ground function, rather
than supplied as a certificate.

Use: `«2610.05164v2».GroundState.exists_unique_ground` uses this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.exists_regular_positive_ground`,
`«2610.05164v2».GroundState.RiccatiData.square_identity` with the arguments shown in the proof.
-/
theorem exists_ground_square_identity {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
    (hM : 0 < ∫ x, m x) : ∃ (u : H1) (R : RiccatiData m (groundParameter hm hn)),
      (∀ x, 0 < H1.rep u x) ∧
      (∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) ∧
      (∀ f : H1, (∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=
        ‖f‖^2-groundParameter hm hn*(∫ x, m x*H1.rep f x^2)) ∧
      densityOperator m u=kernelEigenvalue hm hn 0 • u := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.exists_regular_positive_ground`,
  -- `«2610.05164v2».GroundState.RiccatiData.square_identity` with the arguments shown in the
  -- proof.
  obtain ⟨u,d,hpos,huc,hdu,hdac,_,hbound,hode,he⟩ := exists_regular_positive_ground hm hn hM
  let R := logDerivativeData hpos huc hdu hdac hbound hode
  refine ⟨u,R,hpos,?_,R.square_identity hm,he⟩
  intro x
  change HasDerivAt (H1.rep u) (d x/H1.rep u x*H1.rep u x) x
  rw [div_mul_cancel₀ _ (ne_of_gt (hpos x))]
  exact hdu x

end
end «2610.05164v2».GroundState

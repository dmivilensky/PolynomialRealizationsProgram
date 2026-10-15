import «2610.05164v2».GroundState.LogDerivative

/-!
Article: 2610.05164v2, Theorem 3.1.
The exact equality case of equation (11), with no extra smoothness on f.
Use: `«2610.05164v2».GroundState.RiccatiData.residual_integral_eq_zero_iff_smul` feeds
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff` (square eq zero iff).
Proof chain: `«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff` — 2610.05164v2, Theorem
3.1; Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

namespace RiccatiData
variable {m : ℝ → ℝ} {c : ℝ} (R : RiccatiData m c)

/--
Equivalence of the displayed criteria: `(∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=0 ↔ ∀ᵐ x,
H1.slope f x=R.a x*H1.rep f x`.

Use: `«2610.05164v2».GroundState.RiccatiData.residual_integral_eq_zero_iff_smul` rewrites with
this identity to prove the equivalence `(∫ x, (H1.slope f x-R.a
x*H1.rep f x)^2)=0 ↔ ∃ r : ℝ, f=r • u`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem residual_integral_zero_iff (f : H1) :
    (∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=0 ↔
      ∀ᵐ x, H1.slope f x=R.a x*H1.rep f x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hr : MemLp (fun x => H1.slope f x-R.a x*H1.rep f x) 2 volume :=
    (H1.regular f).derivative_memLp.sub (R.weighted_memLp f)
  rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hr.integrable_sq]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)
  · intro h
    filter_upwards [h] with x hx
    change (H1.slope f x-R.a x*H1.rep f x)^2=0
    simp [hx]

/--
Smoothness to the stated order: `ContDiff ℝ 1 (H1.rep u)`.

Use: `«2610.05164v2».GroundState.RiccatiData.eq_smul_of_residual_zero` uses this assertion to
establish constructs witnesses with the exact properties `∃ r : ℝ, f=r • u`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ground_contDiff {u : H1}
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) : ContDiff ℝ 1 (H1.rep u) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hdu x).differentiableAt,?_⟩
  have he : deriv (H1.rep u)=fun x => R.a x*H1.rep u x := funext (fun x => (hdu x).deriv)
  rw [he]
  exact R.continuous.mul (H1.continuous_rep u)

/--
The zero residual forces a single scalar multiple globally, for every H1 test function, by the
actual AE derivative of f/u and local AC.

Constructs witnesses with the exact properties `∃ r : ℝ, f=r • u`.

Use: `«2610.05164v2».GroundState.RiccatiData.residual_integral_eq_zero_iff_smul` uses this
identity to prove the equivalence `(∫ x, (H1.slope f x-R.a x*H1.rep
f x)^2)=0 ↔ ∃ r : ℝ, f=r • u`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem eq_smul_of_residual_zero {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) (f : H1)
    (hz : ∀ᵐ x, H1.slope f x=R.a x*H1.rep f x) : ∃ r : ℝ, f=r • u := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hi := (R.ground_contDiff hdu).inv (fun x => ne_of_gt (hpos x))
  have hac (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x => H1.rep f x/H1.rep u x) a b := by
    have hua := (hi.contDiffOn : ContDiffOn ℝ 1 (fun x => (H1.rep u x)⁻¹) (uIcc a b)).absolutelyContinuousOnInterval
    apply (((H1.regular f).locally_ac a b).mul hua).congr
    intro x _
    exact (div_eq_mul_inv _ _).symm
  have hd : ∀ᵐ x, HasDerivAt (fun x => H1.rep f x/H1.rep u x) 0 x := by
    filter_upwards [(H1.regular f).derivative_ae,hz] with x hx hxz
    rw [hxz] at hx
    convert hx.div (hdu x) (ne_of_gt (hpos x)) using 1
    ring
  let r : ℝ := H1.rep f 0/H1.rep u 0
  refine ⟨r,H1.rep_injective ?_⟩
  rw [H1.rep_smul]
  funext x
  obtain ⟨k,hk⟩ := (hac 0 x).const_of_ae_hasDerivAt_zero (hd.mono (fun _ hx _ => hx))
  have hx := (hk x right_mem_uIcc).trans (hk 0 left_mem_uIcc).symm
  change H1.rep f x/H1.rep u x=r at hx
  exact (div_eq_iff (ne_of_gt (hpos x))).mp hx

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, H1.slope (r • u) x=R.a
x*H1.rep (r • u) x`.

Use: `«2610.05164v2».GroundState.RiccatiData.residual_integral_eq_zero_iff_smul` uses this
identity to prove the equivalence `(∫ x, (H1.slope f x-R.a x*H1.rep
f x)^2)=0 ↔ ∃ r : ℝ, f=r • u`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem residual_zero_of_smul {u : H1}
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) (r : ℝ) :
    ∀ᵐ x, H1.slope (r • u) x=R.a x*H1.rep (r • u) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [(H1.regular (r • u)).derivative_ae] with x hx
  have hd := (hdu x).const_mul r
  have he : (fun x => r*H1.rep u x)=H1.rep (r • u) := (H1.rep_smul r u).symm
  rw [he] at hd
  have hh := hx.unique hd
  rw [H1.rep_smul]
  change H1.slope (r • u) x=R.a x*(r*H1.rep u x)
  rw [hh]
  ring

/--
The exact equality case of equation (11), with no extra smoothness on f.

Equivalence of the displayed criteria: `(∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=0 ↔ ∃ r : ℝ,
f=r • u`.

Use: `«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff` uses this identity to
establish equivalence of the displayed criteria: `(∫ x, (H1.slope f x-(G.d x/H1.rep G.u
x)*H1.rep f x)^2)=0 ↔ ∃ r : ℝ, f=r • G.u`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_eq_zero_iff`.

Proof: Use the identities/estimates
`«2610.05164v2».GroundState.RiccatiData.residual_integral_zero_iff`,
`«2610.05164v2».GroundState.RiccatiData.eq_smul_of_residual_zero`,
`«2610.05164v2».GroundState.RiccatiData.residual_zero_of_smul` with the arguments shown in the
proof.
-/
theorem residual_integral_eq_zero_iff_smul {u : H1} (hpos : ∀ x, 0 < H1.rep u x)
    (hdu : ∀ x, HasDerivAt (H1.rep u) (R.a x*H1.rep u x) x) (f : H1) :
    (∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=0 ↔ ∃ r : ℝ, f=r • u := by
  -- Use the identities/estimates
  -- `«2610.05164v2».GroundState.RiccatiData.residual_integral_zero_iff`,
  -- `«2610.05164v2».GroundState.RiccatiData.eq_smul_of_residual_zero`,
  -- `«2610.05164v2».GroundState.RiccatiData.residual_zero_of_smul` with the arguments shown in
  -- the proof.
  rw [R.residual_integral_zero_iff]
  constructor
  · exact R.eq_smul_of_residual_zero hpos hdu f
  · rintro ⟨r,rfl⟩
    exact R.residual_zero_of_smul hdu r

end RiccatiData
end
end «2610.05164v2».GroundState

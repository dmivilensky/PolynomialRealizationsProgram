import «2610.05164v2».GroundState.Variational
import «2610.05164v2».GroundState.ExponentialPrimitive

/-!
Article: 2610.05164v2, Theorem 3.1.
Theorem 3.1, equation (11), obtained by integrating the actual total derivative a*f^2.
Use: `«2610.05164v2».GroundState.RiccatiData.square_identity` feeds
`«2610.05164v2».GroundState.GroundWitness.square_identity` (square identity).
Proof chain: `«2610.05164v2».GroundState.GroundWitness.square_identity` — 2610.05164v2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity. The needed
form is proved here.
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
A bounded locally AC logarithmic derivative satisfying the Riccati equation. This interface
states the differential hypotheses explicitly; its square identity is derived below for all H1
test functions.

Use: `«2610.05164v2».GroundState.RiccatiData.continuous` uses this record of data and proof
obligations to establish continuity of the displayed function: `Continuous R.a`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.ground_state`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.
-/
structure RiccatiData (m : ℝ → ℝ) (c : ℝ) where
  /-- Logarithmic derivative of the ground-state candidate. -/
  a : ℝ → ℝ
  /-- The logarithmic derivative remains in [-1,1] pointwise. -/
  bound : ∀ x, |a x| ≤ 1
  /-- Local absolute continuity needed for the square-completion integration argument. -/
  locally_ac : ∀ x y, AbsolutelyContinuousOnInterval a x y
  /-- The Riccati differential equation holds almost everywhere, identifying the density term in square completion. -/
  derivative_ae : ∀ᵐ x, HasDerivAt a (1-c*m x-a x^2) x

namespace RiccatiData
variable {m : ℝ → ℝ} {c : ℝ} (R : RiccatiData m c)

/--
Continuity of the displayed function: `Continuous R.a`.

Use: `«2610.05164v2».GroundState.RiccatiData.weighted_memLp` uses this continuity result to
establish the stated quantitative bound `MemLp (fun x => R.a x*H1.rep f x) 2 volume`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.locallyAC_continuous` with the
arguments shown in the proof.
-/
theorem continuous : Continuous R.a := locallyAC_continuous R.locally_ac

/--
The stated quantitative bound `MemLp (fun x => R.a x*H1.rep f x) 2 volume`.

Use: `«2610.05164v2».GroundState.RiccatiData.squareDerivative_integrable` uses this identity to
establish integrability of the displayed function: `Integrable (R.squareDerivative f)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.regular`,
`«2610.05164v2».GroundState.RiccatiData.continuous`, `«2610.05164v2».Sobolev.H1.continuous_rep`
with the arguments shown in the proof.
-/
theorem weighted_memLp (f : H1) : MemLp (fun x => R.a x*H1.rep f x) 2 volume := by
  apply (H1.regular f).value_memLp.of_le
  · exact (R.continuous.mul (H1.continuous_rep f)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (R.bound x))

/--
Integrability of the displayed function: `Integrable (fun x => R.a x*H1.rep f x^2)`.

Use: `«2610.05164v2».GroundState.RiccatiData.squareDerivative_integral_zero` uses this
integrability result to establish the identity `(∫ x, R.squareDerivative f x)=0`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.regular`,
`«2610.05164v2».GroundState.RiccatiData.continuous`, `«2610.05164v2».Sobolev.H1.continuous_rep`
with the arguments shown in the proof.
-/
theorem weighted_square_integrable (f : H1) : Integrable (fun x => R.a x*H1.rep f x^2) := by
  apply (H1.regular f).value_memLp.integrable_sq.norm.mono'
  · exact (R.continuous.mul ((H1.continuous_rep f).pow 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) (R.bound x))

/--
Defines `squareDerivative` of type `ℝ` by `(1-c*m x-R.a x^2)*H1.rep f x^2+R.a x*(2*(H1.rep f
x*H1.slope f x))`.

Use: `«2610.05164v2».GroundState.RiccatiData.squareDerivative_integrable` uses this definition
to establish integrability of the displayed function: `Integrable (R.squareDerivative f)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.
-/
def squareDerivative (f : H1) (x : ℝ) : ℝ :=
  (1-c*m x-R.a x^2)*H1.rep f x^2+R.a x*(2*(H1.rep f x*H1.slope f x))

/--
Integrability of the displayed function: `Integrable (R.squareDerivative f)`.

Use: `«2610.05164v2».GroundState.RiccatiData.squareDerivative_integral_zero` uses this
integrability result to establish the identity `(∫ x, R.squareDerivative f x)=0`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem squareDerivative_integrable (hm : Integrable m) (f : H1) : Integrable (R.squareDerivative f) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hr : MemLp (fun x => H1.slope f x-R.a x*H1.rep f x) 2 volume :=
    (H1.regular f).derivative_memLp.sub (R.weighted_memLp f)
  have he : R.squareDerivative f=(fun x =>
      (H1.slope f x^2+H1.rep f x^2)-c*(m x*H1.rep f x^2)-
        (H1.slope f x-R.a x*H1.rep f x)^2) := by
    funext x
    dsimp [squareDerivative]
    ring
  rw [he]
  exact (((H1.regular f).derivative_memLp.integrable_sq.add
    (H1.regular f).value_memLp.integrable_sq).sub
    ((«2610.05164v2».GroundState.weighted_square_integrable hm f).const_mul c)).sub hr.integrable_sq

/--
Exact identity `(∫ x, R.squareDerivative f x)=0`.

Use: `«2610.05164v2».GroundState.RiccatiData.square_identity` rewrites with this identity to
establish the precise assertion is `(∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)= ‖f‖^2-c*(∫ x, m
x*H1.rep f x^2)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem squareDerivative_integral_zero (hm : Integrable m) (f : H1) :
    (∫ x, R.squareDerivative f x)=0 := by
  -- Use the proved fundamental theorem of calculus with its explicit integrability and
  -- endpoint hypotheses.
  apply locallyAC_integral_derivative_zero (R.weighted_square_integrable f)
    (R.squareDerivative_integrable hm f)
  · intro a b
    apply ((R.locally_ac a b).mul ((H1.regular f).square_locallyAC a b)).congr
    intro x _
    rfl
  · filter_upwards [R.derivative_ae,(H1.regular f).square_derivative_ae] with x ha hf
    exact ha.mul hf

/--
Theorem 3.1, equation (11), obtained by integrating the actual total derivative a*f^2. All
boundary and integrability obligations are discharged.

The precise assertion is `(∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)= ‖f‖^2-c*(∫ x, m x*H1.rep f
x^2)`.

Use: `«2610.05164v2».Comparison.groundParameter_reflection` uses this identity to establish
exact identity `groundParameter (reflected_integrable hm) (reflected_nonneg hn)=groundParameter
hm hn`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: 2610.05164v2, Appendix C.1 — ground-state transform and sharp square identity.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem square_identity (hm : Integrable m) (f : H1) :
    (∫ x, (H1.slope f x-R.a x*H1.rep f x)^2)=
      ‖f‖^2-c*(∫ x, m x*H1.rep f x^2) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hr : MemLp (fun x => H1.slope f x-R.a x*H1.rep f x) 2 volume :=
    (H1.regular f).derivative_memLp.sub (R.weighted_memLp f)
  -- Establish hE as the integrability justification for the later integral estimates or
  -- changes of order.
  have hE : Integrable (fun x => H1.slope f x^2+H1.rep f x^2) :=
    (H1.regular f).derivative_memLp.integrable_sq.add (H1.regular f).value_memLp.integrable_sq
  have he (x : ℝ) : R.squareDerivative f x+(H1.slope f x-R.a x*H1.rep f x)^2=
      (H1.slope f x^2+H1.rep f x^2)-c*(m x*H1.rep f x^2) := by
    dsimp [squareDerivative]
    ring
  have hi := integral_congr_ae (μ := volume) (Filter.Eventually.of_forall he)
  rw [integral_add (R.squareDerivative_integrable hm f) hr.integrable_sq,
    R.squareDerivative_integral_zero hm,zero_add,
    integral_sub hE ((«2610.05164v2».GroundState.weighted_square_integrable hm f).const_mul c),
    integral_const_mul,
    integral_add (H1.regular f).derivative_memLp.integrable_sq (H1.regular f).value_memLp.integrable_sq,
    ← H1.norm_sq_energy] at hi
  exact hi

end RiccatiData
end
end «2610.05164v2».GroundState

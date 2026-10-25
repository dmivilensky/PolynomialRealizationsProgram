import chebyshev2.Calibration.ReferenceAmplitude

/-!
Article: chebyshev2, Section 4.1.
The rational positive nondecreasing reference profiles of Definition 7(i).
Use: `chebyshev2.DualCertificate.RationalReference.referenceData` feeds
`chebyshev2.DualCertificate.Data.Gamma_symmetric` (Gamma symmetric).
Proof chain: `chebyshev2.DualCertificate.Data.Admissible` — chebyshev2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set chebyshev2.Calibration
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/--
A positive rational reference profile with finitely many positive pole terms and positive
offsets. The proof fields keep its denominators nonzero and its base contribution positive.

Use: `chebyshev2.DualCertificate.RationalReference.coefficient` uses this record of data
and proof obligations in the displayed construction of `coefficient`. Its inputs and component
formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
structure RationalReference where
  /-- Number of rational poles/terms in the reference profile. -/
  count : ℕ
  /-- Strictly positive constant term of the reference profile. -/
  p₀ : ℚ
  /-- Positive rational coefficient of each pole term. -/
  p : Fin count → ℚ
  /-- Positive rational pole offset, keeping denominators away from zero on the physical domain. -/
  ζ : Fin count → ℚ
  /-- The constant reference contribution is strictly positive. -/
  p₀_pos : 0 < p₀
  /-- Every pole coefficient is strictly positive. -/
  p_pos : ∀ i, 0 < p i
  /-- Every pole offset is strictly positive. -/
  ζ_pos : ∀ i, 0 < ζ i

namespace RationalReference
variable (R : RationalReference)

/--
Defines `coefficient` of type `ℝ` by `(R.p₀:ℝ)+∑ i, (R.p i:ℝ)*Q/(Q+(R.ζ i:ℝ))`.

Use: `chebyshev2.DualCertificate.RationalReference.coefficient_monotone` uses this
definition to establish monotonicity in increasing order: `MonotoneOn R.coefficient (Ici
(0:ℝ))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def coefficient (Q : ℝ) : ℝ := (R.p₀:ℝ)+∑ i, (R.p i:ℝ)*Q/(Q+(R.ζ i:ℝ))

/--
The stated quantitative bound `0 < R.coefficient Q`.

Use: `chebyshev2.DualCertificate.RationalReference.referenceData` uses this bound in the
displayed construction of `referenceData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem coefficient_positive {Q : ℝ} (hQ : 0 ≤ Q) : 0 < R.coefficient Q := by
  have hp : (0:ℝ)<R.p₀ := by exact_mod_cast R.p₀_pos
  have hz (i) : (0:ℝ)<R.ζ i := by exact_mod_cast R.ζ_pos i
  have hi (i) : (0:ℝ)<R.p i := by exact_mod_cast R.p_pos i
  exact add_pos_of_pos_of_nonneg hp (Finset.sum_nonneg (fun i _ =>
    div_nonneg (mul_nonneg (hi i).le hQ) (by linarith [hz i])))

/--
Monotonicity in increasing order: `MonotoneOn R.coefficient (Ici (0:ℝ))`.

Use: `chebyshev2.DualCertificate.RationalReference.referenceData` uses this assertion in
the displayed construction of `referenceData`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coefficient_monotone : MonotoneOn R.coefficient (Ici (0:ℝ)) := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  intro x hx y hy hxy
  dsimp only [coefficient]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  have hz : (0:ℝ)<R.ζ i := by exact_mod_cast R.ζ_pos i
  have hp : (0:ℝ)<R.p i := by exact_mod_cast R.p_pos i
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have dx : 0<x+(R.ζ i:ℝ) := by linarith [hx]
  have dy : 0<y+(R.ζ i:ℝ) := by linarith [hy]
  apply (div_le_div_iff₀ dx dy).2
  have h := mul_nonneg (mul_nonneg hp.le hz.le) (sub_nonneg.mpr hxy)
  nlinarith

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ R.coefficient (Ici (0:ℝ))`.

Use: `chebyshev2.DualCertificate.RationalReference.referenceData` uses this assertion in
the displayed construction of `referenceData`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem coefficient_smooth : ContDiffOn ℝ ∞ R.coefficient (Ici (0:ℝ)) := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  apply contDiffOn_const.add
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.div (contDiffOn_const.mul contDiffOn_id)
    (contDiffOn_id.add contDiffOn_const)
  intro x hx
  change 0 ≤ x at hx
  have hz : (0:ℝ)<R.ζ i := by exact_mod_cast R.ζ_pos i
  exact ne_of_gt (by linarith [hx] : 0<x+(R.ζ i:ℝ))

/--
Constructs `referenceData` of type `ReferenceData` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.DualCertificate.Data.referenceData` uses this definition in the displayed
construction of `referenceData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def referenceData {k : ℝ} (hk : 0 < k) : ReferenceData where
  k := k
  k_positive := hk
  b := R.coefficient
  smooth := R.coefficient_smooth.mono (fun _ hx => hx.1)
  positive := fun _ hx => R.coefficient_positive hx.1
  monotone := R.coefficient_monotone.mono (fun _ hx => hx.1)

end RationalReference
end
end chebyshev2.DualCertificate

import «2610.05164v2».Packing.Blocks
import «2610.05164v2».Green.Intervals
import «2610.05164v2».Finite.Gain

/-!
Article: 2610.05164v2, Theorem 2.3.
The exact normalization and energy part of Theorem 2.3 for an irreducible fiber element.
Use: `«2610.05164v2».Packing.NormalizedCompactDensity` feeds
`«2610.05164v2».Packing.Jacobi.density_normalized` (The exact normalization and energy part of
Theorem 2.3 for an irreducible fiber element).
Proof chain: `«2610.05164v2».Packing.packedDensity_normalized` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Packing
noncomputable section
open Set MeasureTheory Real
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/--
The continuum class Mc in Section 2.2, as properties of actual functions.

Use: `«2610.05164v2».Packing.Jacobi.density_normalized` uses this definition to establish the
precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.
-/
def NormalizedCompactDensity (m : ℝ → ℝ) : Prop :=
  Measurable m ∧ (∀ x, 0 ≤ m x) ∧ MemLp m ⊤ volume ∧ HasCompactSupport m ∧
    (∫ x, m x) = 1 ∧ (∫ x, sqrt (m x)) = 1

namespace Jacobi
variable {N : ℕ} (J : «2610.05164v2».Jacobi N)

/--
Constructs `blocks` of type `Blocks (Fin N)` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Packing.Jacobi.density` uses this definition in the displayed construction
of `density`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3.
-/
def blocks (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) : Blocks (Fin N) where
  left := J.intervalLeft hN
  right := J.intervalRight hN
  height := fun i => J.green i i / N
  left_le_right i := by
    have h := J.interval_length hN i
    have hd := J.green_diagonal_pos hN ht i
    linarith [one_div_pos.mpr hd]
  height_nonneg i := div_nonneg (J.green_diagonal_pos hN ht i).le (Nat.cast_nonneg _)
  disjoint i j hij := by
    apply Set.disjoint_left.mpr
    intro x hi hj
    have hc := J.contractive_of_pencils (J.one_sub_posDef hN ht) (J.one_add_posDef hN ht)
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have ho := J.intervals_ordered hN hc hir i j hlt
      exact (not_lt_of_ge (hi.2.trans ho)) hj.1
    · have ho := J.intervals_ordered hN hc hir j i hgt
      exact (not_lt_of_ge (hj.2.trans ho)) hi.1

/--
Defines `density` of type `ℝ → ℝ` by `(blocks J hN ht hir).closedDensity`.

Use: `«2610.05164v2».Packing.Jacobi.density_energy` rewrites with this definition to establish
exact identity `(∫ x, density J hN ht hir x ^ (3 / 2 : ℝ)) = J.energy / (N : ℝ)^3`.

Article: 2610.05164v2, Theorem 2.3.
-/
def density (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) : ℝ → ℝ :=
  (blocks J hN ht hir).closedDensity

/--
Exact identity `density J hN ht hir x = ∑ i : Fin N, (J.packingInterval hN i).indicator (fun _
=> J.green i i ^ 2 / (N : ℝ)^2) x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem density_formula (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) (x : ℝ) :
    density J hN ht hir x = ∑ i : Fin N,
      (J.packingInterval hN i).indicator (fun _ => J.green i i ^ 2 / (N : ℝ)^2) x := by
  simp only [density, Blocks.closedDensity, blocks, «2610.05164v2».Jacobi.packingInterval, div_pow]

/--
Exact identity `(∫ x, density J hN ht hir x) = 1`.

Use: `«2610.05164v2».Packing.Jacobi.density_normalized` uses this identity to establish the
precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Article: 2610.05164v2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_mass (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∫ x, density J hN ht hir x) = 1 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [density, Blocks.closed_mass]
  have he (i : Fin N) : (J.green i i / N)^2 * (J.intervalRight hN i-J.intervalLeft hN i) =
      J.green i i / (N : ℝ)^2 := by
    rw [J.interval_length hN i]
    field_simp [(J.green_diagonal_pos hN ht i).ne']
  change (∑ i : Fin N, (J.green i i / N)^2 * (J.intervalRight hN i-J.intervalLeft hN i)) = 1
  simp_rw [he]
  rw [← Finset.sum_div]
  change Matrix.trace J.green / (N : ℝ)^2 = 1
  rw [J.green_trace hN ht, div_self]
  exact pow_ne_zero 2 (Nat.cast_ne_zero.mpr hN.ne')

/--
Exact identity `(∫ x, sqrt (density J hN ht hir x)) = 1`.

Use: `«2610.05164v2».Packing.Jacobi.density_normalized` uses this identity to establish the
precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Article: 2610.05164v2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_root_mass (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∫ x, sqrt (density J hN ht hir x)) = 1 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [density, Blocks.closed_root_mass]
  change (∑ i : Fin N, J.green i i / N * (J.intervalRight hN i-J.intervalLeft hN i)) = 1
  have he (i : Fin N) : J.green i i / N * (J.intervalRight hN i-J.intervalLeft hN i) = 1/(N : ℝ) := by
    rw [J.interval_length hN i]
    field_simp [(J.green_diagonal_pos hN ht i).ne']
  simp_rw [he]
  simp [Nat.cast_ne_zero.mpr hN.ne']

/--
Exact identity `(∫ x, density J hN ht hir x ^ (3 / 2 : ℝ)) = J.energy / (N : ℝ)^3`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_energy (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    (∫ x, density J hN ht hir x ^ (3 / 2 : ℝ)) = J.energy / (N : ℝ)^3 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [density, Blocks.closed_energy]
  change (∑ i : Fin N, (J.green i i / N)^3 * (J.intervalRight hN i-J.intervalLeft hN i)) = _
  have he (i : Fin N) : (J.green i i / N)^3 * (J.intervalRight hN i-J.intervalLeft hN i) =
      J.green i i ^ 2 / (N : ℝ)^3 := by
    rw [J.interval_length hN i]
    field_simp [(J.green_diagonal_pos hN ht i).ne']
  simp_rw [he]
  exact (Finset.sum_div _ _ _).symm

/--
The exact normalization and energy part of Theorem 2.3 for an irreducible fiber element.

The precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Blocks.closedDensity_measurable`,
`«2610.05164v2».Packing.Blocks.closedDensity_nonneg`,
`«2610.05164v2».Packing.Blocks.closedDensity_bound` with the arguments shown in the proof.
-/
theorem density_normalized (hN : 0 < N) (ht : J.Terminal) (hir : J.Irreducible) :
    NormalizedCompactDensity (density J hN ht hir) := by
  -- Use the identities/estimates `«2610.05164v2».Packing.Blocks.closedDensity_measurable`,
  -- `«2610.05164v2».Packing.Blocks.closedDensity_nonneg`,
  -- `«2610.05164v2».Packing.Blocks.closedDensity_bound` with the arguments shown in the proof.
  let B := blocks J hN ht hir
  refine ⟨B.closedDensity_measurable, B.closedDensity_nonneg, ?_, B.closedDensity_compactSupport,
    density_mass J hN ht hir, density_root_mass J hN ht hir⟩
  apply memLp_top_of_bound B.closedDensity_measurable.aestronglyMeasurable (∑ i, B.height i^2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (B.closedDensity_nonneg x)]
    exact B.closedDensity_bound x)

end Jacobi
end
end «2610.05164v2».Packing

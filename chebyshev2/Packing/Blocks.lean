import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-!
Article: chebyshev2, Theorem 2.3.
Finite interval data.
Use: `chebyshev2.Packing.Blocks.closed_energy` feeds
`chebyshev2.Packing.Representation.density_energy` (density energy).
Proof chain: `chebyshev2.Packing.packedDensity_energy` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Packing
noncomputable section
open Set MeasureTheory Real
open scoped BigOperators

/--
Finite interval data. Half-open cells remove endpoint overlaps; the paper's closed-interval
density is proved equal almost everywhere below.

Use: `chebyshev2.Packing.Blocks.amplitude` uses this record of data and proof obligations
in the displayed construction of `amplitude`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.
-/
structure Blocks (ι : Type*) where
  /-- Left endpoint of each density block. -/
  left : ι → ℝ
  /-- Right endpoint of each density block. -/
  right : ι → ℝ
  /-- Constant nonnegative density height on each block. -/
  height : ι → ℝ
  /-- Every block has nonnegative length. -/
  left_le_right : ∀ i, left i ≤ right i
  /-- Every block height is nonnegative. -/
  height_nonneg : ∀ i, 0 ≤ height i
  /-- Half-open block intervals are pairwise disjoint, so their masses and energy contributions add. -/
  disjoint : Pairwise fun i j => Disjoint (Ioc (left i) (right i)) (Ioc (left j) (right j))

namespace Blocks
variable {ι : Type*} [Fintype ι] (B : Blocks ι)

/--
Defines `amplitude` of type `ℝ` by `∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ =>
B.height i) x`.

Use: `chebyshev2.Packing.Blocks.power_amplitude` rewrites with this definition to establish
exact identity `B.amplitude x ^ p = ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ =>
B.height i ^ p) x`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.
-/
def amplitude (x : ℝ) : ℝ := ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i) x
/--
Defines `density` of type `ℝ` by `∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ =>
B.height i ^ 2) x`.

Use: `chebyshev2.Packing.Blocks.energy_rpow` uses this definition to establish exact
identity `(∫ x, B.density x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.
-/
def density (x : ℝ) : ℝ := ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i ^ 2) x
/--
Defines `closedDensity` of type `ℝ` by `∑ i, (Icc (B.left i) (B.right i)).indicator (fun _ =>
B.height i ^ 2) x`.

Use: `chebyshev2.Packing.Blocks.closedDensity_measurable` uses this definition to establish
measurability of the displayed map: `Measurable B.closedDensity`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.
-/
def closedDensity (x : ℝ) : ℝ :=
  ∑ i, (Icc (B.left i) (B.right i)).indicator (fun _ => B.height i ^ 2) x

/--
The stated quantitative bound `0 ≤ B.amplitude x`.

Use: `chebyshev2.Packing.Blocks.sqrt_density` rewrites with this bound to establish exact
identity `sqrt (B.density x) = B.amplitude x`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem amplitude_nonneg (x : ℝ) : 0 ≤ B.amplitude x := by
  apply Finset.sum_nonneg
  intro i _
  exact indicator_nonneg (fun _ _ => B.height_nonneg i) x

/--
Exact identity `B.amplitude x ^ p = ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ =>
B.height i ^ p) x`.

Use: `chebyshev2.Packing.Blocks.density_eq_square` uses this identity to establish exact
identity `B.density x = B.amplitude x ^ 2`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Separate `∃ i, x ∈ Ioc (B.left i) (B.right i)` from its negation; prove the goal under
each of these mutually exclusive hypotheses.
-/
theorem power_amplitude (p : ℕ) (hp : p ≠ 0) (x : ℝ) :
    B.amplitude x ^ p = ∑ i, (Ioc (B.left i) (B.right i)).indicator (fun _ => B.height i ^ p) x := by
  -- Separate `∃ i, x ∈ Ioc (B.left i) (B.right i)` from its negation; prove the goal under
  -- each of these mutually exclusive hypotheses.
  classical
  by_cases hx : ∃ i, x ∈ Ioc (B.left i) (B.right i)
  · obtain ⟨i, hi⟩ := hx
    have hz (j : ι) (hji : j ≠ i) : x ∉ Ioc (B.left j) (B.right j) := by
      intro hj
      exact Set.disjoint_left.mp (B.disjoint hji) hj hi
    have hs (q : ℕ) :
        (∑ j, (Ioc (B.left j) (B.right j)).indicator (fun _ => B.height j ^ q) x) = B.height i ^ q := by
      rw [Finset.sum_eq_single i (fun j _ hji => indicator_of_notMem (hz j hji) _) (by simp)]
      exact indicator_of_mem hi _
    have ha : B.amplitude x = B.height i := by
      simpa [amplitude] using hs 1
    rw [ha, hs]
  · have hz : ∀ i, x ∉ Ioc (B.left i) (B.right i) := by simpa using hx
    simp [amplitude, indicator_of_notMem, hz, hp]

/--
Exact identity `B.density x = B.amplitude x ^ 2`.

Use: `chebyshev2.Packing.Blocks.density_nonneg` rewrites with this identity to establish
the stated quantitative bound `0 ≤ B.density x`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.power_amplitude` with the
arguments shown in the proof.
-/
theorem density_eq_square (x : ℝ) : B.density x = B.amplitude x ^ 2 :=
  (B.power_amplitude 2 (by norm_num) x).symm

/--
The stated quantitative bound `0 ≤ B.density x`.

Use: `chebyshev2.Packing.Blocks.energy_rpow` rewrites with this bound to establish exact
identity `(∫ x, B.density x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.density_eq_square` with the
arguments shown in the proof.
-/
theorem density_nonneg (x : ℝ) : 0 ≤ B.density x := by rw [B.density_eq_square]; positivity

/--
Exact identity `sqrt (B.density x) = B.amplitude x`.

Use: `chebyshev2.Packing.Blocks.energy` rewrites with this identity to establish exact
identity `(∫ x, B.density x * sqrt (B.density x)) = ∑ i, B.height i ^ 3 * (B.right i - B.left
i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.density_eq_square`,
`chebyshev2.Packing.Blocks.amplitude_nonneg` with the arguments shown in the proof.
-/
theorem sqrt_density (x : ℝ) : sqrt (B.density x) = B.amplitude x := by rw [B.density_eq_square, sqrt_sq (B.amplitude_nonneg x)]

/--
Exact identity `(∫ x, B.amplitude x ^ p) = ∑ i, B.height i ^ p * (B.right i - B.left i)`.

Use: `chebyshev2.Packing.Blocks.energy` uses this identity to establish the identity `(∫
x, B.density x * sqrt (B.density x)) = ∑ i, B.height i ^ 3 * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem integral_power (p : ℕ) (hp : p ≠ 0) :
    (∫ x, B.amplitude x ^ p) = ∑ i, B.height i ^ p * (B.right i - B.left i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  simp_rw [B.power_amplitude p hp]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator measurableSet_Ioc, setIntegral_const,
      volume_real_Ioc_of_le (B.left_le_right i)]
    simp [mul_comm]
  · intro i _
    exact (integrableOn_const (hs := by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top) :
      IntegrableOn (fun _ : ℝ => B.height i ^ p)
      (Ioc (B.left i) (B.right i)) volume).integrable_indicator measurableSet_Ioc

/--
Exact identity `(∫ x, B.density x) = ∑ i, B.height i ^ 2 * (B.right i - B.left i)`.

Use: `chebyshev2.Packing.Blocks.closed_mass` uses this identity to establish the identity
`(∫ x, B.closedDensity x) = ∑ i, B.height i ^ 2 * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.density_eq_square`,
`chebyshev2.Packing.Blocks.integral_power` with the arguments shown in the proof.
-/
theorem mass : (∫ x, B.density x) =
    ∑ i, B.height i ^ 2 * (B.right i - B.left i) := by
  simp_rw [B.density_eq_square]
  exact B.integral_power 2 (by norm_num)

/--
Exact identity `(∫ x, sqrt (B.density x)) = ∑ i, B.height i * (B.right i - B.left i)`.

Use: `chebyshev2.Packing.Blocks.closed_root_mass` uses this identity to establish exact
identity `(∫ x, sqrt (B.closedDensity x)) = ∑ i, B.height i * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.sqrt_density`,
`chebyshev2.Packing.Blocks.integral_power` with the arguments shown in the proof.
-/
theorem root_mass : (∫ x, sqrt (B.density x)) =
    ∑ i, B.height i * (B.right i - B.left i) := by
  simp_rw [B.sqrt_density]
  simpa using B.integral_power 1 (by norm_num)

/--
Exact identity `(∫ x, B.density x * sqrt (B.density x)) = ∑ i, B.height i ^ 3 * (B.right i -
B.left i)`.

Use: `chebyshev2.Packing.Blocks.energy_rpow` uses this identity to establish the identity
`(∫ x, B.density x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.sqrt_density`,
`chebyshev2.Packing.Blocks.density_eq_square`,
`chebyshev2.Packing.Blocks.integral_power` with the arguments shown in the proof.
-/
theorem energy : (∫ x, B.density x * sqrt (B.density x)) =
    ∑ i, B.height i ^ 3 * (B.right i - B.left i) := by
  simp_rw [B.sqrt_density, B.density_eq_square, ← pow_succ]
  exact B.integral_power 3 (by norm_num)

/--
Exact identity `(∫ x, B.density x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left
i)`.

Use: `chebyshev2.Packing.Blocks.closed_energy` uses this identity to establish exact
identity `(∫ x, B.closedDensity x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left
i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.

Proof: Use the identities/estimates `chebyshev2.Packing.Blocks.density_nonneg`,
`chebyshev2.Packing.Blocks.energy` with the arguments shown in the proof.
-/
theorem energy_rpow : (∫ x, B.density x ^ (3 / 2 : ℝ)) =
    ∑ i, B.height i ^ 3 * (B.right i - B.left i) := by
  have he (x : ℝ) : B.density x ^ (3 / 2 : ℝ) = B.density x * sqrt (B.density x) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add' (B.density_nonneg x) (by norm_num : (1 + 1 / 2 : ℝ) ≠ 0),
      rpow_one, ← sqrt_eq_rpow]
  simp_rw [he]
  exact B.energy

/--
The precise assertion is `B.closedDensity =ᵐ[volume] B.density`.

Use: `chebyshev2.Packing.Blocks.closed_energy` uses this identity to establish exact
identity `(∫ x, B.closedDensity x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i - B.left
i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem closedDensity_ae : B.closedDensity =ᵐ[volume] B.density := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hx : ∀ᵐ x : ℝ ∂volume, ∀ i : ι, x ≠ B.left i := by
    exact ae_all_iff.mpr (fun i => volume.ae_ne (B.left i))
  filter_upwards [hx] with x hx
  apply Finset.sum_congr rfl
  intro i _
  have hm : x ∈ Icc (B.left i) (B.right i) ↔ x ∈ Ioc (B.left i) (B.right i) := by
    simp only [mem_Icc, mem_Ioc]
    exact and_congr_left (fun _ => lt_iff_le_and_ne.trans (by simp [hx i, ne_comm])) |>.symm
  simp only [indicator, hm]

/--
The stated quantitative bound `0 ≤ B.closedDensity x`.

Use: `chebyshev2.Calibration.Data.packed_energy_ge_base` uses this bound to establish the
stated quantitative bound `C.base (packedCoupling J hN ht)
(chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem closedDensity_nonneg (x : ℝ) : 0 ≤ B.closedDensity x := by
  apply Finset.sum_nonneg
  intro i _
  exact indicator_nonneg (fun _ _ => sq_nonneg _) x

/--
The stated quantitative bound `B.closedDensity x ≤ ∑ i, B.height i ^ 2`.

Use: `chebyshev2.Calibration.Data.packed_energy_ge_base` uses this bound to establish the
stated quantitative bound `C.base (packedCoupling J hN ht)
(chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Separate `x ∈ Icc (B.left i) (B.right i)` from its negation; prove the goal under each
of these mutually exclusive hypotheses.
-/
theorem closedDensity_bound (x : ℝ) : B.closedDensity x ≤ ∑ i, B.height i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x ∈ Icc (B.left i) (B.right i)
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx, sq_nonneg]

/--
Measurability of the displayed map: `Measurable B.closedDensity`.

Use: `chebyshev2.Packing.Jacobi.density_normalized` uses this measurability result to
establish the precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem closedDensity_measurable : Measurable B.closedDensity := by
  unfold closedDensity
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Icc)

/--
Integrability of the displayed function: `Integrable B.closedDensity`.

Use: `chebyshev2.Calibration.Data.packed_energy_ge_base` uses this integrability result to
establish the stated quantitative bound `C.base (packedCoupling J hN ht)
(chebyshev2.Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem closedDensity_integrable : Integrable B.closedDensity := by
  apply integrable_finsetSum
  intro i _
  exact (integrableOn_const (hs := by rw [volume_Icc]; exact ENNReal.ofReal_ne_top) :
    IntegrableOn (fun _ : ℝ => B.height i ^ 2) (Icc (B.left i) (B.right i)) volume).integrable_indicator
      measurableSet_Icc

/--
The precise assertion is `HasCompactSupport B.closedDensity`.

Use: `chebyshev2.Packing.Jacobi.density_normalized` uses this assertion to establish the
precise assertion is `NormalizedCompactDensity (density J hN ht hir)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem closedDensity_compactSupport : HasCompactSupport B.closedDensity := by
  apply HasCompactSupport.intro (isCompact_iUnion (fun i : ι =>
    (isCompact_Icc : IsCompact (Icc (B.left i) (B.right i)))))
  intro x hx
  apply Finset.sum_eq_zero
  intro i _
  exact indicator_of_notMem (fun hi => hx (mem_iUnion.mpr ⟨i, hi⟩)) _

/--
Exact identity `(∫ x, B.closedDensity x) = ∑ i, B.height i ^ 2 * (B.right i - B.left i)`.

Use: `chebyshev2.Packing.Blocks.density_atomic_transport` uses this identity to establish
the stated quantitative bound `TraceBound (densityOperator B.closedDensity - atomicOperator
(fun i => B.height i^2 * (B.right i-B.left i)) y) (2 * sqrt (2 * (∫ x, B.closedDensity x) * ∫
z, |z.1-z.2| ∂B.coupling y))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem closed_mass : (∫ x, B.closedDensity x) =
    ∑ i, B.height i ^ 2 * (B.right i - B.left i) :=
  (integral_congr_ae B.closedDensity_ae).trans B.mass

/--
Exact identity `(∫ x, sqrt (B.closedDensity x)) = ∑ i, B.height i * (B.right i - B.left i)`.

Use: `chebyshev2.Packing.Jacobi.density_root_mass` rewrites with this identity to establish
exact identity `(∫ x, sqrt (density J hN ht hir x)) = 1`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_normalized`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem closed_root_mass : (∫ x, sqrt (B.closedDensity x)) =
    ∑ i, B.height i * (B.right i - B.left i) := by
  apply Eq.trans (integral_congr_ae ?_) B.root_mass
  filter_upwards [B.closedDensity_ae] with x hx
  rw [hx]

/--
Exact identity `(∫ x, B.closedDensity x ^ (3 / 2 : ℝ)) = ∑ i, B.height i ^ 3 * (B.right i -
B.left i)`.

Use: `chebyshev2.Packing.Jacobi.density_energy` rewrites with this identity to establish
exact identity `(∫ x, density J hN ht hir x ^ (3 / 2 : ℝ)) = J.energy / (N : ℝ)^3`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packedDensity_energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem closed_energy : (∫ x, B.closedDensity x ^ (3 / 2 : ℝ)) =
    ∑ i, B.height i ^ 3 * (B.right i - B.left i) := by
  apply Eq.trans (integral_congr_ae ?_) B.energy_rpow
  filter_upwards [B.closedDensity_ae] with x hx
  rw [hx]

end Blocks
end
end chebyshev2.Packing

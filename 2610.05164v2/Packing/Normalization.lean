import «2610.05164v2».Packing.Existence
import «2610.05164v2».Packing.IrreducibleTransport
import «2610.05164v2».Continuum.MatrixTraceBound

/-!
Article: 2610.05164v2, Theorem 2.3.
Normalization.
Use: `«2610.05164v2».Packing.Representation.density_atomic_traceBound` feeds
`«2610.05164v2».Packing.packed_spectral_distance` (Theorem 2.3, equation (7), for the full fiber
including zero edges).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Packing
noncomputable section
open «2610.05164v2».Continuum MeasureTheory Real Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} {J : «2610.05164v2».Jacobi N} {gap : ℝ}

namespace Representation
variable (P : Representation J.green gap)

/--
Constructs `blocks` of type `Blocks (Fin N)` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Packing.Representation.coupling_cost_bound` uses this definition to
establish the stated quantitative bound `(∫ z, |z.1-z.2| ∂(P.blocks hN).coupling P.point) ≤
1/(2*(N : ℝ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def blocks (_hN : 0 < N) : Blocks (Fin N) where
  left := P.left
  right := P.right
  height i := J.green i i/N
  left_le_right i := by linarith [P.length i,one_div_pos.mpr (P.diagonal_pos i)]
  height_nonneg i := div_nonneg (P.diagonal_pos i).le (Nat.cast_nonneg _)
  disjoint := P.disjoint

/--
Defines `density` of type `ℝ → ℝ` by `(P.blocks hN).closedDensity`.

Use: `«2610.05164v2».Packing.Representation.density_energy` rewrites with this definition to
establish exact identity `(∫ x, P.density hN x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.
-/
def density (hN : 0 < N) : ℝ → ℝ := (P.blocks hN).closedDensity

/--
Exact identity `(P.blocks hN).height i^2 * ((P.blocks hN).right i-(P.blocks hN).left i) =
Jacobi.atomicWeight J i`.

Use: `«2610.05164v2».Packing.Representation.density_atomic_traceBound` rewrites with this
identity to establish `TraceBound (densityOperator (P.density
hN)-atomicOperator (Jacobi.atomicWeight J) P.point) (2/sqrt (N : ℝ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem blocks_weight (hN : 0 < N) (i : Fin N) :
    (P.blocks hN).height i^2 * ((P.blocks hN).right i-(P.blocks hN).left i) = Jacobi.atomicWeight J i := by
  change (J.green i i/N)^2 * (P.right i-P.left i) = _
  rw [P.length]
  unfold Jacobi.atomicWeight
  field_simp [(P.diagonal_pos i).ne']

/--
Exact identity `(∫ x, P.density hN x) = 1`.

Use: `«2610.05164v2».Packing.Representation.density_atomic_traceBound` uses this identity to
establish the precise assertion is `TraceBound (densityOperator (P.density hN)-atomicOperator
(Jacobi.atomicWeight J) P.point) (2/sqrt (N : ℝ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Blocks.closed_mass`,
`«2610.05164v2».Packing.Representation.blocks_weight`, `«2610.05164v2».Jacobi.green_trace` with
the arguments shown in the proof.
-/
theorem density_mass (hN : 0 < N) (ht : J.Terminal) : (∫ x, P.density hN x) = 1 := by
  rw [density,Blocks.closed_mass]
  simp_rw [P.blocks_weight hN]
  unfold Jacobi.atomicWeight
  rw [← Finset.sum_div]
  change Matrix.trace J.green / (N : ℝ)^2 = 1
  rw [J.green_trace hN ht,div_self (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hN.ne'))]

/--
Exact identity `(∫ x, sqrt (P.density hN x)) = 1`.

Use: `«2610.05164v2».Packing.Representation.density_normalized` uses this identity to establish
the precise assertion is `NormalizedCompactDensity (P.density hN)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_root_mass (hN : 0 < N) : (∫ x, sqrt (P.density hN x)) = 1 := by
  rw [density,Blocks.closed_root_mass]
  change (∑ i : Fin N, J.green i i/N * (P.right i-P.left i)) = 1
  have he (i : Fin N) : J.green i i/N * (P.right i-P.left i) = 1/(N : ℝ) := by
    rw [P.length]
    field_simp [(P.diagonal_pos i).ne']
  simp_rw [he]
  simp [Nat.cast_ne_zero.mpr hN.ne']

/--
Exact identity `(∫ x, P.density hN x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3`.

Use: `«2610.05164v2».Packing.packedDensity_energy` uses this identity to establish exact
identity `(∫ x, packedDensity J hN ht x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_energy`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_energy (hN : 0 < N) :
    (∫ x, P.density hN x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [density,Blocks.closed_energy]
  change (∑ i : Fin N, (J.green i i/N)^3 * (P.right i-P.left i)) = _
  have he (i : Fin N) : (J.green i i/N)^3 * (P.right i-P.left i) = J.green i i^2/(N : ℝ)^3 := by
    rw [P.length]
    field_simp [(P.diagonal_pos i).ne']
  simp_rw [he]
  exact (Finset.sum_div _ _ _).symm

/--
The precise assertion is `NormalizedCompactDensity (P.density hN)`.

Use: `«2610.05164v2».Packing.packedDensity_normalized` uses this assertion to establish the
precise assertion is `NormalizedCompactDensity (packedDensity J hN ht)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Blocks.closedDensity_measurable`,
`«2610.05164v2».Packing.Blocks.closedDensity_nonneg`,
`«2610.05164v2».Packing.Blocks.closedDensity_bound` with the arguments shown in the proof.
-/
theorem density_normalized (hN : 0 < N) (ht : J.Terminal) : NormalizedCompactDensity (P.density hN) := by
  let B := P.blocks hN
  refine ⟨B.closedDensity_measurable,B.closedDensity_nonneg,?_,B.closedDensity_compactSupport,
    P.density_mass hN ht,P.density_root_mass hN⟩
  apply memLp_top_of_bound B.closedDensity_measurable.aestronglyMeasurable (∑ i, B.height i^2)
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (B.closedDensity_nonneg x)]
    exact B.closedDensity_bound x)

/--
The stated quantitative bound `(∫ z, |z.1-z.2| ∂(P.blocks hN).coupling P.point) ≤ 1/(2*(N :
ℝ))`.

Use: `«2610.05164v2».Packing.Representation.density_atomic_traceBound` uses this bound to
establish the precise assertion is `TraceBound (densityOperator (P.density hN)-atomicOperator
(Jacobi.atomicWeight J) P.point) (2/sqrt (N : ℝ))`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem coupling_cost_bound (hN : 0 < N) :
    (∫ z, |z.1-z.2| ∂(P.blocks hN).coupling P.point) ≤ 1/(2*(N : ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (P.blocks hN).coupling_cost P.point P.point_mem
  have he (i : Fin N) : (P.blocks hN).height i^2 *
      ((P.blocks hN).right i-(P.blocks hN).left i)^2/2 = 1/(2*(N : ℝ)^2) := by
    change (J.green i i/N)^2 * (P.right i-P.left i)^2/2 = _
    rw [P.length]
    field_simp [(P.diagonal_pos i).ne',Nat.cast_ne_zero.mpr hN.ne']
  simp_rw [he] at h
  have hs : (∑ _i : Fin N, 1/(2*(N : ℝ)^2)) = 1/(2*(N : ℝ)) := by
    simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul]
    field_simp
  exact h.trans_eq hs

/--
The precise assertion is `TraceBound (densityOperator (P.density hN)-atomicOperator
(Jacobi.atomicWeight J) P.point) (2/sqrt (N : ℝ))`.

Use: `«2610.05164v2».Packing.packed_spectral_distance` uses this assertion to establish the
stated quantitative bound `(∑' j, |packedEigenvalue J hN ht j-finiteEigenvalue N j|) ≤ 2/sqrt
(N : ℝ)+1/(N : ℝ)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem density_atomic_traceBound (hN : 0 < N) (ht : J.Terminal) :
    TraceBound (densityOperator (P.density hN)-atomicOperator (Jacobi.atomicWeight J) P.point) (2/sqrt (N : ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have h := (P.blocks hN).density_atomic_transport P.point
  simp_rw [P.blocks_weight hN] at h
  have hm : (∫ x, (P.blocks hN).closedDensity x) = 1 := P.density_mass hN ht
  rw [hm] at h
  apply h.mono
  have hcost := P.coupling_cost_bound hN
  have he : 2 * sqrt (2 * 1 * (1/(2*(N : ℝ)))) = 2/sqrt (N : ℝ) := by
    rw [show 2 * 1 * (1/(2*(N : ℝ))) = (N : ℝ)⁻¹ by field_simp]
    rw [sqrt_inv,div_eq_mul_inv]
  rw [← he]
  apply mul_le_mul_of_nonneg_left (sqrt_le_sqrt ?_) (by norm_num)
  nlinarith

end Representation
end
end «2610.05164v2».Packing

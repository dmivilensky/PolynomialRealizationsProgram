import «2610.05164v2».Packing.MatrixError
import «2610.05164v2».Continuum.DistanceTriangle
import «2610.05164v2».Continuum.ReferenceDeterminant

/-!
Article: 2610.05164v2, Proposition 6.
The printed error tends to zero, independently of every matrix in the fiber.
Use: `«2610.05164v2».Packing.transferError_tendsto_zero` feeds
`«2610.05164v2».Calibration.Data.packedObservation_tendsto` (packed Observation tendsto).
Proof chain: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` — 2610.05164v2,
Theorem E.1; Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Packing
noncomputable section
open «2610.05164v2».Continuum MeasureTheory Real Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ} (J : «2610.05164v2».Jacobi N)

/--
A fixed actual packing, chosen from the proved construction for every fiber matrix, with the
article's gap between distinct irreducible blocks.

Use: `«2610.05164v2».Packing.packedDensity` uses this definition in the displayed construction
of `packedDensity`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.
-/
def packing (hN : 0 < N) (ht : J.Terminal) : Representation J.green (2*log (N : ℝ)) :=
  Classical.choice (exists_representation N J
    (J.contractive_of_pencils (J.one_sub_posDef hN ht) (J.one_add_posDef hN ht)) _
    (mul_nonneg (by norm_num) (log_nonneg (by exact_mod_cast hN))))

/--
Defines `packedDensity` of type `ℝ → ℝ` by `(packing J hN ht).density hN`.

Use: `«2610.05164v2».Packing.packedDensity_formula` rewrites with this definition to establish
exact identity `packedDensity J hN ht x = ∑ i : Fin N, (Icc ((packing J hN ht).left i)
((packing J hN ht).right i)).indicator (fun _ => J.green i i^2/(N : ℝ)^2) x`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packedDensity_normalized`.
-/
def packedDensity (hN : 0 < N) (ht : J.Terminal) : ℝ → ℝ := (packing J hN ht).density hN

/--
Defines `packedEigenvalue` of type `ℕ → ℝ` by `kernelEigenvalue ((packing J hN ht).blocks
hN).closedDensity_integrable ((packing J hN ht).blocks hN).closedDensity_nonneg`.

Use: `«2610.05164v2».Packing.packedEigenvalue_zero_pos` uses this definition to establish the
stated quantitative bound `0 < packedEigenvalue J hN ht 0`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.
-/
def packedEigenvalue (hN : 0 < N) (ht : J.Terminal) : ℕ → ℝ :=
  kernelEigenvalue ((packing J hN ht).blocks hN).closedDensity_integrable
    ((packing J hN ht).blocks hN).closedDensity_nonneg

/--
Exact identity `packedDensity J hN ht x = ∑ i : Fin N, (Icc ((packing J hN ht).left i)
((packing J hN ht).right i)).indicator (fun _ => J.green i i^2/(N : ℝ)^2) x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 6.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem packedDensity_formula (hN : 0 < N) (ht : J.Terminal) (x : ℝ) :
    packedDensity J hN ht x = ∑ i : Fin N,
      (Icc ((packing J hN ht).left i) ((packing J hN ht).right i)).indicator
        (fun _ => J.green i i^2/(N : ℝ)^2) x := by
  simp only [packedDensity,Representation.density,Blocks.closedDensity,Representation.blocks,div_pow]

/--
The precise assertion is `NormalizedCompactDensity (packedDensity J hN ht)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Representation.density_normalized`
with the arguments shown in the proof.
-/
theorem packedDensity_normalized (hN : 0 < N) (ht : J.Terminal) :
    NormalizedCompactDensity (packedDensity J hN ht) := (packing J hN ht).density_normalized hN ht

/--
Exact identity `(∫ x, packedDensity J hN ht x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3`.

Use: `«2610.05164v2».Calibration.Data.packed_energy_ge_base` rewrites with this identity to
establish the stated quantitative bound `C.base (packedCoupling J hN ht)
(«2610.05164v2».Packing.packedLogDeterminant J hN ht (C.sigma*packedCoupling J hN ht)) ≤
J.normalizedEnergy`.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Representation.density_energy` with
the arguments shown in the proof.
-/
theorem packedDensity_energy (hN : 0 < N) (ht : J.Terminal) :
    (∫ x, packedDensity J hN ht x ^ (3/2 : ℝ)) = J.energy/(N : ℝ)^3 :=
  (packing J hN ht).density_energy hN

/--
The stated quantitative bound `0 ≤ packedEigenvalue J hN ht j`.

Use: `«2610.05164v2».Packing.packedEigenvalue_zero_pos` uses this bound to establish the stated
quantitative bound `0 < packedEigenvalue J hN ht 0`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_nonneg` with the arguments shown in
the proof.
-/
theorem packedEigenvalue_nonneg (hN : 0 < N) (ht : J.Terminal) (j : ℕ) : 0 ≤ packedEigenvalue J hN ht j :=
  (kernelSpectralData _ _).eigenvalue_nonneg j

/--
Summability of the displayed sequence: `Summable (packedEigenvalue J hN ht)`.

Use: `«2610.05164v2».Packing.packed_ground_parameter_distance` uses this summability result to
establish the stated quantitative bound `|2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤
4*transferError N/(referenceEigenvalue 0)^2`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Use the identities/estimates
`«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_summable` with the arguments shown in
the proof.
-/
theorem packedEigenvalue_summable (hN : 0 < N) (ht : J.Terminal) : Summable (packedEigenvalue J hN ht) :=
  (kernelSpectralData _ _).eigenvalue_summable

/--
Exact identity `(∑' j, packedEigenvalue J hN ht j) = 1`.

Use: `«2610.05164v2».Packing.packedEigenvalue_zero_pos` uses this identity to establish the
stated quantitative bound `0 < packedEigenvalue J hN ht 0`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.kernelEigenvalue_mass`,
`«2610.05164v2».Packing.Representation.density_mass` with the arguments shown in the proof.
-/
theorem packedEigenvalue_mass (hN : 0 < N) (ht : J.Terminal) : (∑' j, packedEigenvalue J hN ht j) = 1 :=
  (kernelEigenvalue_mass _ _).trans ((packing J hN ht).density_mass hN ht)

/--
The stated quantitative bound `0 < packedEigenvalue J hN ht 0`.

Use: `«2610.05164v2».Calibration.Data.packedCoupling_positive` uses this bound to establish the
stated quantitative bound `0 < packedCoupling J hN ht`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem packedEigenvalue_zero_pos (hN : 0 < N) (ht : J.Terminal) : 0 < packedEigenvalue J hN ht 0 := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  by_contra h
  have hz (j : ℕ) : packedEigenvalue J hN ht j = 0 := by
    apply le_antisymm
    · exact ((kernelSpectralData _ _).eigenvalue_antitone (Nat.zero_le j)).trans (le_of_not_gt h)
    · exact packedEigenvalue_nonneg J hN ht j
  have hm := packedEigenvalue_mass J hN ht
  simp only [hz,tsum_zero] at hm
  norm_num at hm

/--
Theorem 2.3, equation (7), for the full fiber including zero edges.

The stated quantitative bound `(∑' j, |packedEigenvalue J hN ht j-finiteEigenvalue N j|) ≤
2/sqrt (N : ℝ)+1/(N : ℝ)`.

Use: `«2610.05164v2».Packing.packed_reference_distance` uses this bound to establish the stated
quantitative bound `(∑' j, |packedEigenvalue J hN ht j-referenceEigenvalue j|) ≤ transferError
N`.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Packing.Blocks.closedDensity_integrable`,
`«2610.05164v2».Packing.Blocks.closedDensity_nonneg`,
`«2610.05164v2».Packing.Jacobi.atomicWeight_pos` with the arguments shown in the proof.
-/
theorem packed_spectral_distance (hN : 0 < N) (ht : J.Terminal) :
    (∑' j, |packedEigenvalue J hN ht j-finiteEigenvalue N j|) ≤ 2/sqrt (N : ℝ)+1/(N : ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».Packing.Blocks.closedDensity_integrable`,
  -- `«2610.05164v2».Packing.Blocks.closedDensity_nonneg`,
  -- `«2610.05164v2».Packing.Jacobi.atomicWeight_pos` with the arguments shown in the proof.
  let P := packing J hN ht
  let hm := (P.blocks hN).closedDensity_integrable
  let hn := (P.blocks hN).closedDensity_nonneg
  let w := Jacobi.atomicWeight J
  let hw := fun i => (Jacobi.atomicWeight_pos J hN ht i).le
  let D := atomicMatrixSpectralData w P.point
  have h1 := eigenvalue_l1_le_traceBound (densityOperator_isCompact hm)
    (atomicOperator_isCompact _ _ hw) (densityOperator_positive hm hn)
    (atomicOperator_positive _ _ hw) (densitySpectralData hm hn)
    (atomicSpectralData _ _ hw) (P.density_atomic_traceBound hN ht)
  rw [density_kernel_eigenvalue_eq hm hn,atomic_matrix_eigenvalue_eq] at h1
  have hpG : (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isPositive_toEuclideanLin_iff.mpr (normalizedGreen_posSemidef J hN ht)
  have hpD : (Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix w P.point)).IsPositive := by
    rw [atomicMatrix_operator]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self _
  have h2 := eigenvalue_l1_le_traceBound (isCompactOperator_of_locallyCompactSpace_dom _)
    (isCompactOperator_of_locallyCompactSpace_dom _) hpG hpD (greenSpectralData J hN ht) D
    (P.atomic_matrix_traceBound_logGap hN ht)
  rw [green_eigenvalue_eq] at h2
  have he : (∑' j, |D.eigenvalue j-finiteEigenvalue N j|) ≤ 1/(N : ℝ) := by
    simpa only [abs_sub_comm] using h2
  exact (spectral_distance_triangle (packedEigenvalue_summable J hN ht) D.eigenvalue_summable
    (finiteEigenvalue_summable N)).trans (add_le_add h1 he)

/--
The error constant printed in Theorem 2.4.

Use: `«2610.05164v2».Packing.packed_ground_parameter_distance` uses this definition to
establish the stated quantitative bound `|2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤
4*transferError N/(referenceEigenvalue 0)^2`.

Article: 2610.05164v2, Theorem 2.4 via `«2610.05164v2».Packing.packed_reference_distance`.
-/
def transferError (N : ℕ) : ℝ := 2/sqrt (N : ℝ)+1/(N : ℝ)+8/(Real.pi^2*(2*(N : ℝ)-1))

/--
Theorem 2.4, equation (8).

The stated quantitative bound `(∑' j, |packedEigenvalue J hN ht j-referenceEigenvalue j|) ≤
transferError N`.

Use: `«2610.05164v2».Packing.packed_ground_parameter_distance` uses this bound to establish the
stated quantitative bound `|2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤ 4*transferError
N/(referenceEigenvalue 0)^2`.

Article: 2610.05164v2, Theorem 2.4.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectral_distance_triangle`,
`«2610.05164v2».Packing.packedEigenvalue_summable`,
`«2610.05164v2».Continuum.finiteEigenvalue_summable` with the arguments shown in the proof.
-/
theorem packed_reference_distance (hN : 0 < N) (ht : J.Terminal) :
    (∑' j, |packedEigenvalue J hN ht j-referenceEigenvalue j|) ≤ transferError N :=
  (spectral_distance_triangle (packedEigenvalue_summable J hN ht) (finiteEigenvalue_summable N)
    summable_reference).trans (add_le_add (packed_spectral_distance J hN ht)
      (finite_reference_distance_bound hN))

/--
The Fredholm observation is evaluated on the actual continuum spectrum.

Use: `«2610.05164v2».Packing.packed_logDeterminant_distance` rewrites with this definition to
establish the stated quantitative bound `|packedLogDeterminant J hN ht s-log (cosh (sqrt s))| ≤
s/2*transferError N`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def packedLogDeterminant (hN : 0 < N) (ht : J.Terminal) (s : ℝ) : ℝ :=
  logDeterminant (packedEigenvalue J hN ht) s

/--
Theorem 2.4, equation (9): determinant transfer.

The stated quantitative bound `|packedLogDeterminant J hN ht s-log (cosh (sqrt s))| ≤
s/2*transferError N`.

Use: `«2610.05164v2».Calibration.Data.packedObservation_tendsto` uses this bound to establish
the limit stated in that declaration.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_fredholm_observation_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.reference_logDeterminant`,
`«2610.05164v2».Continuum.logDeterminant_distance`,
`«2610.05164v2».Packing.packedEigenvalue_summable` with the arguments shown in the proof.
-/
theorem packed_logDeterminant_distance (hN : 0 < N) (ht : J.Terminal) {s : ℝ} (hs : 0 ≤ s) :
    |packedLogDeterminant J hN ht s-log (cosh (sqrt s))| ≤ s/2*transferError N := by
  rw [packedLogDeterminant,← reference_logDeterminant hs]
  exact (logDeterminant_distance (packedEigenvalue_summable J hN ht) summable_reference
    (packedEigenvalue_nonneg J hN ht) (fun j => (referenceEigenvalue_pos j).le) hs).trans
    (mul_le_mul_of_nonneg_left (packed_reference_distance J hN ht) (by positivity))

/--
Theorem 2.4, equation (9): the quadratic trace observation.

The stated quantitative bound `|(∑' j, packedEigenvalue J hN ht j^2)-(2/3 : ℝ)| ≤
2*transferError N`.

Use: `«2610.05164v2».DualCertificate.packed_trace_tendsto` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun n => ∑' j,
(packedEigenvalue (J n).val (by omega) (J n).property j)^2) atTop (𝓝 (2/3:ℝ))`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packed_square_integral_distance`.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.reference_square_mass`,
`«2610.05164v2».Continuum.square_trace_distance`,
`«2610.05164v2».Packing.packedEigenvalue_summable` with the arguments shown in the proof.
-/
theorem packed_square_trace_distance (hN : 0 < N) (ht : J.Terminal) :
    |(∑' j, packedEigenvalue J hN ht j^2)-(2/3 : ℝ)| ≤ 2*transferError N := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.reference_square_mass`,
  -- `«2610.05164v2».Continuum.square_trace_distance`,
  -- `«2610.05164v2».Packing.packedEigenvalue_summable` with the arguments shown in the proof.
  rw [← reference_square_mass]
  apply (square_trace_distance (packedEigenvalue_summable J hN ht) summable_reference
    (packedEigenvalue_nonneg J hN ht) (fun j => (referenceEigenvalue_pos j).le) ?_ ?_).trans
    (mul_le_mul_of_nonneg_left (packed_reference_distance J hN ht) (by norm_num))
  · intro j
    rw [← packedEigenvalue_mass J hN ht]
    exact (packedEigenvalue_summable J hN ht).le_tsum j (fun i _ => packedEigenvalue_nonneg J hN ht i)
  · intro j
    rw [← reference_mass]
    exact summable_reference.le_tsum j (fun i _ => (referenceEigenvalue_pos i).le)

/--
Theorem 2.4, equation (9): the reciprocal leading eigenvalue.

The stated quantitative bound `|2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤ 4*transferError
N/(referenceEigenvalue 0)^2`.

Use: `«2610.05164v2».Calibration.Data.packedCoupling_tendsto` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
packedCoupling (J n).val (by omega) (J n).property) atTop (𝓝 (Real.pi^2/4))`.

Article: 2610.05164v2, Theorem 2.4.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem packed_ground_parameter_distance (hN : 0 < N) (ht : J.Terminal)
    (hδ : transferError N < referenceEigenvalue 0/2) :
    |2/packedEigenvalue J hN ht 0-Real.pi^2/4| ≤ 4*transferError N/(referenceEigenvalue 0)^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hd : |packedEigenvalue J hN ht 0-referenceEigenvalue 0| ≤ transferError N :=
    (((packedEigenvalue_summable J hN ht).sub summable_reference).abs.le_tsum 0
      (fun _ _ => abs_nonneg _)).trans (packed_reference_distance J hN ht)
  have he : 2/referenceEigenvalue 0 = Real.pi^2/4 := by
    unfold referenceEigenvalue
    field_simp [Real.pi_ne_zero]
    norm_num
  simpa only [he] using ground_parameter_distance (referenceEigenvalue_pos 0) hd hδ

/--
The printed error tends to zero, independently of every matrix in the fiber.

The precise assertion is `Filter.Tendsto transferError Filter.atTop (nhds 0)`.

Use: `«2610.05164v2».Calibration.Data.packedCoupling_tendsto` uses this assertion to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
packedCoupling (J n).val (by omega) (J n).property) atTop (𝓝 (Real.pi^2/4))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem transferError_tendsto_zero : Filter.Tendsto transferError Filter.atTop (nhds 0) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop
  have hr := tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp hn)
  have hi := tendsto_inv_atTop_zero.comp hn
  have hd : Filter.Tendsto (fun n : ℕ => 2*(n : ℝ)-1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro r
    filter_upwards [hn.eventually (Filter.eventually_ge_atTop ((r+1)/2))] with n hn
    linarith
  have hp := tendsto_inv_atTop_zero.comp (Filter.Tendsto.const_mul_atTop (sq_pos_of_pos pi_pos) hd)
  convert ((hr.const_mul 2).add hi).add (hp.const_mul 8) using 1 <;>
    first | (funext n; simp only [transferError,div_eq_mul_inv,Function.comp_def,one_mul]) | norm_num

end
end «2610.05164v2».Packing

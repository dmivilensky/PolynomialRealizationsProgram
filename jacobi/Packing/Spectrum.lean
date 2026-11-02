import jacobi.Packing.Mass
import chebyshev2.Continuum.DistanceTriangle

/-!
Article: jacobi, Proposition 3.1.
The full packing theorem for arbitrary contractive Jacobi matrices. The actual
matrix spectrum, rather than the Chebyshev reference spectrum, is retained.
The gap is chosen from the scaled trace; thus reducible chains obey exactly the
printed bound 4√(μ/N), with no restrictions on the number or size of blocks.
Use: the existing block separation construction accepts this gap.
-/

namespace jacobi.Packing
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum
open chebyshev2.Packing MeasureTheory Real Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {N : ℕ}

/-- Nonnegative gap balancing the atomic and spreading errors at arbitrary mass.
Use: the existing block separation construction accepts this gap.
Article: jacobi, Proposition 3.1.
-/
def separation (N : ℕ) (μ : ℝ) : ℝ :=
  max 0 (log ((N : ℝ) * μ / (2 * sqrt (μ / (N : ℝ)))))

/-- The selected separation makes the cross-block error at most 2√(μ/N).
Use: combines with the identical spreading bound to give the constant four.
Article: jacobi, Proposition 3.1.
Proof: exponentiating minus the maximum is at most the reciprocal ratio. -/
theorem separation_error (hN : 0 < N) {μ : ℝ} (hμ : 0 < μ) :
    exp (-separation N μ) * (N : ℝ) * μ ≤ 2 * sqrt (μ / (N : ℝ)) := by
  -- The maximum with zero gives a nonnegative gap whose exponential has the required reciprocal upper bound.
  have hroot : 0 < sqrt (μ / (N : ℝ)) := sqrt_pos.mpr (div_pos hμ (Nat.cast_pos.mpr hN))
  have hratio : 0 < (N : ℝ) * μ / (2 * sqrt (μ / (N : ℝ))) := by positivity
  have he : exp (-separation N μ) ≤
      ((N : ℝ) * μ / (2 * sqrt (μ / (N : ℝ))))⁻¹ := by
    calc
      _ ≤ exp (-log ((N : ℝ) * μ / (2 * sqrt (μ / (N : ℝ))))) :=
        exp_le_exp.mpr (neg_le_neg (le_max_right _ _))
      _ = _ := by rw [exp_neg, exp_log hratio]
  calc
    _ = exp (-separation N μ) * ((N : ℝ) * μ) := by ring
    _ ≤ ((N : ℝ) * μ / (2 * sqrt (μ / (N : ℝ))))⁻¹ * ((N : ℝ) * μ) :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = _ := by field_simp

/-- A concrete packing chosen from the existing all-block existence theorem.
Use: supplies the density, intervals and spectral estimates below.
Article: jacobi, Proposition 3.1.
-/
def packing (J : Jacobi N) (hc : opNorm J.matrix < 1) :
    Representation J.green (separation N (mass J)) :=
  Classical.choice (exists_representation N J hc _ (le_max_left _ _))

/-- The actual scaled resolvent matrix is positive, independently of its spectrum.
Use: extracts its ordered eigenvalues with the existing finite spectral theory.
Article: jacobi, Lemma 1.3.
Proof: contractivity gives I − J positive definite; invert and scale. -/
theorem normalizedGreen_positive (J : Jacobi N) (hc : opNorm J.matrix < 1) :
    J.normalizedGreen.PosSemidef :=
  (J.pencils_of_contractive hc).1.inv.posSemidef.smul (by positivity)

/-- The descending spectrum of N⁻²(I − J)⁻¹, padded with zeros.
Use: the packing compares with this actual spectrum for every input matrix.
Article: jacobi, Proposition 3.1.
-/
def finiteEigenvalue (J : Jacobi N) (hc : opNorm J.matrix < 1) : ℕ → ℝ :=
  (matrixSpectralData J.normalizedGreen (normalizedGreen_positive J hc)).eigenvalue

/-- The density spreading the resolvent diagonal over the constructed intervals.
Use: is the admissible continuum density in the spectral transfer argument.
Article: jacobi, Proposition 3.1.
-/
def density (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) : ℝ → ℝ :=
  (packing J hc).density hN

/-- Eigenvalues of the genuine exponential-kernel operator of the packed density.
Use: connects the interval construction to continuum spectral constraints.
Article: jacobi, Proposition 3.1.
-/
def packedEigenvalue (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) : ℕ → ℝ :=
  kernelEigenvalue ((packing J hc).blocks hN).closedDensity_integrable
    ((packing J hc).blocks hN).closedDensity_nonneg

/-- Full spectral estimate, including arbitrarily many zero couplings.
Use: the uniform error needed to transfer any fibre with convergent edge spectra.
Article: jacobi, Proposition 3.1.
Proof: compare density to atoms, atoms to the actual matrix, and add the errors. -/
theorem spectral_distance (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    (∑' j, |packedEigenvalue J hc hN j - finiteEigenvalue J hc j|) ≤
      4 * sqrt (mass J / (N : ℝ)) := by
  let P := packing J hc
  let hm := (P.blocks hN).closedDensity_integrable
  let hn := (P.blocks hN).closedDensity_nonneg
  let w := chebyshev2.Packing.Jacobi.atomicWeight J
  have hw (i : Fin N) : 0 ≤ w i := div_nonneg (P.diagonal_pos i).le (sq_nonneg _)
  let D := atomicMatrixSpectralData w P.point
  -- The continuum and atomic operators live in the same feature Hilbert space.
  have h1 := eigenvalue_l1_le_traceBound (densityOperator_isCompact hm)
    (atomicOperator_isCompact _ _ hw) (densityOperator_positive hm hn)
    (atomicOperator_positive _ _ hw) (densitySpectralData hm hn)
    (atomicSpectralData _ _ hw) (density_atomic_traceBound P hN)
  rw [density_kernel_eigenvalue_eq hm hn, atomic_matrix_eigenvalue_eq] at h1
  have hpG : (Matrix.toEuclideanCLM (𝕜 := ℝ) J.normalizedGreen).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isPositive_toEuclideanLin_iff.mpr (normalizedGreen_positive J hc)
  have hpD : (Matrix.toEuclideanCLM (𝕜 := ℝ) (atomicMatrix w P.point)).IsPositive := by
    rw [atomicMatrix_operator]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self _
  -- The second comparison is finite-dimensional; eigenvalues use the same sorting.
  let G := matrixSpectralData J.normalizedGreen (normalizedGreen_positive J hc)
  have h2 := eigenvalue_l1_le_traceBound (isCompactOperator_of_locallyCompactSpace_dom _)
    (isCompactOperator_of_locallyCompactSpace_dom _) hpG hpD G D
    (atomic_matrix_traceBound P hN)
  have h2' : (∑' j, |D.eigenvalue j - G.eigenvalue j|) ≤
      exp (-separation N (mass J)) * (N : ℝ) * mass J := by
    simpa only [abs_sub_comm] using h2
  have h := (spectral_distance_triangle (kernelSpectralData hm hn).eigenvalue_summable
    D.eigenvalue_summable G.eigenvalue_summable).trans (add_le_add h1 h2')
  exact h.trans (by linarith [separation_error hN (mass_pos P hN)])

/-- The density is exactly the sum over the printed closed intervals.
Use: identifies the formal operator with the literal density in the article.
Article: jacobi, Proposition 3.1.
Proof: unfold the existing spreading construction. -/
theorem density_formula (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) (x : ℝ) :
    density J hc hN x = ∑ i : Fin N,
      (Icc ((packing J hc).left i) ((packing J hc).right i)).indicator
        (fun _ => J.green i i^2 / (N : ℝ)^2) x := by
  simp only [density, Representation.density, Blocks.closedDensity, Representation.blocks, div_pow]

/-- All three volume identities hold for this same spectrally controlled density.
Use: makes the packed density admissible for the later continuum relaxations.
Article: jacobi, Proposition 3.1.
Proof: reuse the cell integration results, generalizing only the mass. -/
theorem volume_identities (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    (∫ x, density J hc hN x) = mass J ∧
    (∫ x, sqrt (density J hc hN x)) = 1 ∧
    (∫ x, density J hc hN x ^ (3/2 : ℝ)) = J.energy / (N : ℝ)^3 :=
  ⟨density_mass (packing J hc) hN, (packing J hc).density_root_mass hN,
    (packing J hc).density_energy hN⟩

/-- The packed density is a genuine nonnegative integrable compactly supported function.
Use: licenses the continuum spectral construction and all later variational constraints.
Article: jacobi, Proposition 3.1.
Proof: reuse regularity of the finite closed-interval spreading construction. -/
theorem density_properties (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    Measurable (density J hc hN) ∧ (∀ x, 0 ≤ density J hc hN x) ∧
      Integrable (density J hc hN) ∧ HasCompactSupport (density J hc hN) :=
  ⟨((packing J hc).blocks hN).closedDensity_measurable,
    ((packing J hc).blocks hN).closedDensity_nonneg,
    ((packing J hc).blocks hN).closedDensity_integrable,
    ((packing J hc).blocks hN).closedDensity_compactSupport⟩

/-- The same packed density has spectral mass exactly equal to the scaled finite trace.
Use: prevents losing the mass identity when passing from cells to the actual kernel spectrum.
Article: jacobi, Proposition 3.1.
Proof: the existing continuum trace theorem equals the already established volume identity. -/
theorem packed_spectral_mass (J : Jacobi N) (hc : opNorm J.matrix < 1) (hN : 0 < N) :
    (∑' j, packedEigenvalue J hc hN j) = mass J := by
  have h := kernelEigenvalue_mass ((packing J hc).blocks hN).closedDensity_integrable
    ((packing J hc).blocks hN).closedDensity_nonneg
  exact h.trans (density_mass (packing J hc) hN)

end
end jacobi.Packing

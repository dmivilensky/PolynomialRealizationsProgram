import jacobi.Packing.VariationalDensity
import jacobi.Finite.OrderedBasis

/-!
Article: jacobi, Lemma 1.3.
Every actual fibre matrix has the padded sequence 1/[N^2(1-zeta_k)] as
its ordered normalized Green spectrum. An actual ordered eigenbasis is
constructed by the finite theory; the resolvent uses the same basis, and
the existing positive matrix spectral uniqueness theorem identifies the
sorted sequence used in packing. No resolvent enumeration is assumed.
Source: finite real spectral theorem and spectral functional calculus.
Use: defines the common finite-fibre spectral sequence occurring in the Transfer hypothesis.
-/
namespace jacobi.Packing
noncomputable section
open chebyshev1 chebyshev2 chebyshev2.Continuum
open jacobi.Finite Matrix Polynomial
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

/-- The scaled resolvent value at each prescribed descending node.
Use: defines the common finite-fibre spectral sequence occurring in the Transfer hypothesis.
Article: jacobi, Lemma 1.3.
-/
def nodeResolvent (S : Nodes N) (k : Fin N) : ℝ := (1-S.value k)⁻¹/(N : ℝ)^2

/-- The node-resolvent spectrum padded by zero after the matrix dimension.
Use: expresses convergence of the actual finite spectra in the same l1 space as the limiting edge spectrum.
Article: jacobi, Lemma 1.3.
-/
def fibreSpectrum (S : Nodes N) (j : ℕ) : ℝ :=
  if h : j < N then nodeResolvent S ⟨j,h⟩ else 0

/-- Every scaled resolvent node is strictly positive for a nonempty chain.
Use: the sorted diagonal spectrum has no spurious zero before its finite support ends.
Article: jacobi, Lemma 1.3.
Proof: each node lies below one and N squared is strictly positive. -/
theorem nodeResolvent_pos (S : Nodes N) (hN : 0 < N) (k : Fin N) : 0 < nodeResolvent S k :=
  div_pos (inv_pos.mpr (sub_pos.mpr (S.interval k).2)) (pow_pos (Nat.cast_pos.mpr hN) 2)

/-- Resolvent nodes retain the article's strict descending order.
Use: the community spectral sorting agrees with the prescribed terminal-root enumeration.
Article: jacobi, Lemma 1.3.
Proof: descending nodes give ascending positive denominators, so inversion reverses their order. -/
theorem nodeResolvent_strictAnti (S : Nodes N) (hN : 0 < N) : StrictAnti (nodeResolvent S) := by
  intro i j hij
  apply div_lt_div_of_pos_right _ (pow_pos (Nat.cast_pos.mpr hN) 2)
  exact inv_strictAnti₀ (sub_pos.mpr (S.interval i).2) (by linarith [S.strictAnti hij])

/-- The actual normalized resolvent has an explicit spectral basis at the prescribed nodes.
Use: proves its characteristic polynomial and ordered spectrum for every member of the fibre.
Article: jacobi, Lemma 1.3.
-/
def normalizedGreenBasis (S : Nodes N) (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    SpectralBasis J.normalizedGreen where
  Q := (orderedBasis S J hJ).Q
  eigenvalues := nodeResolvent S
  transpose_mul := (orderedBasis S J hJ).transpose_mul
  mul_transpose := (orderedBasis S J hJ).mul_transpose
  diagonalize := by
    -- The same orthogonal coordinates diagonalize J and every resolvent of J.
    let B := orderedBasis S J hJ
    have hne (i : Fin N) : 1-B.eigenvalues i ≠ 0 := by
      rw [orderedBasis_values]
      exact (sub_pos.mpr (S.interval i).2).ne'
    have h := SpectralCoordinates.coordinates_resolvent B hne
    change B.Q.transpose*J.normalizedGreen*B.Q=Matrix.diagonal (nodeResolvent S)
    rw [Jacobi.normalizedGreen,Matrix.mul_smul,Matrix.smul_mul]
    change ((N : ℝ)^2)⁻¹ • B.coordinates J.green=Matrix.diagonal (nodeResolvent S)
    rw [Jacobi.green,h]
    simp only [B,orderedBasis_values]
    ext i j
    by_cases hij : i=j <;> simp [hij,nodeResolvent,div_eq_mul_inv,mul_comm]

/-- Every actual fibre member has exactly the prescribed padded scaled-resolvent spectrum.
Use: the packing error is uniform over the complete polynomial fibre in the full Transfer theorem.
Article: jacobi, Theorem D.4.
Proof: the explicit resolvent basis identifies its characteristic polynomial
with the diagonal node-resolvent matrix. Positive spectral uniqueness and
strict sorting give precisely the zero-padded article sequence. -/
theorem finiteEigenvalue_eq_fibreSpectrum (S : Nodes N) (hN : 0 < N)
    (J : Jacobi N) (hJ : InFiber J S.polynomial) :
    finiteEigenvalue J (S.contractive hJ)=fibreSpectrum S := by
  -- The characteristic polynomial comes from an actual resolvent basis, not an assumed eigenvalue list.
  let a := nodeResolvent S
  have ha (i : Fin N) : 0 ≤ a i := (nodeResolvent_pos S hN i).le
  have he : J.normalizedGreen.charpoly=(Matrix.diagonal a).charpoly := by
    rw [(normalizedGreenBasis S J hJ).charpoly_factor,Matrix.charpoly_diagonal]
    rfl
  change (matrixSpectralData J.normalizedGreen _).eigenvalue=_
  rw [matrix_eigenvalue_eq_of_charpoly _ _ (normalizedGreen_positive J (S.contractive hJ))
    (Matrix.posSemidef_diagonal_iff.mpr ha) he,diagonal_matrix_eigenvalue a ha]
  funext j
  exact spectralSorted_fin (nodeResolvent_strictAnti S hN) (nodeResolvent_pos S hN) Summable.of_finite j

/-- The padded fibre sequence is exactly the community's sorted finite node-resolvent spectrum.
Use: gives summability, nonnegativity and the exact common spectral mass without selecting a fibre matrix.
Article: jacobi, Theorem D.4.
Proof: strict descending positivity identifies finite spectral sorting point by point. -/
theorem fibreSpectrum_eq_sorted (S : Nodes N) (hN : 0 < N) :
    fibreSpectrum S=spectralSorted (Summable.of_finite (f := nodeResolvent S)) := by
  funext j
  exact (spectralSorted_fin (nodeResolvent_strictAnti S hN) (nodeResolvent_pos S hN) Summable.of_finite j).symm

/-- The actual padded fibre spectrum is summable.
Use: its l1 distance and trace are legitimate in the arbitrary-spectrum Transfer theorem.
Article: jacobi, Lemma 1.3.
Proof: finite spectral sorting preserves summability. -/
theorem fibreSpectrum_summable (S : Nodes N) (hN : 0 < N) : Summable (fibreSpectrum S) := by
  rw [fibreSpectrum_eq_sorted S hN]
  exact spectralSorted_summable Summable.of_finite (fun i => (nodeResolvent_pos S hN i).le)

/-- The actual padded fibre spectrum is nonnegative at every index.
Use: spectral mass and second-moment errors follow from the same nonnegative l1 estimates.
Article: jacobi, Theorem D.4.
Proof: before the dimension cutoff use positive resolvent nodes; afterwards the value is zero. -/
theorem fibreSpectrum_nonneg (S : Nodes N) (hN : 0 < N) (j : ℕ) : 0 ≤ fibreSpectrum S j := by
  unfold fibreSpectrum
  split_ifs with h
  · exact (nodeResolvent_pos S hN ⟨j,h⟩).le
  · exact le_refl 0

/-- Every fibre member has the same actual scaled trace, equal to the sum of its padded resolvent sequence.
Use: the packing error is uniformly 4sqrt(mu_N/N), with mu_N independent of the chosen fibre matrix.
Article: jacobi, Lemma 1.3.
Proof: diagonalize the resolvent in the proved ordered basis and sum its trace;
finite spectral sorting preserves the sum of the scaled nodes. -/
theorem mass_eq_fibreSpectrum (S : Nodes N) (hN : 0 < N)
    (J : Jacobi N) (hJ : InFiber J S.polynomial) : mass J=∑' j, fibreSpectrum S j := by
  -- Both trace identities concern the actual inverse I-J and the prescribed terminal roots.
  let B := orderedBasis S J hJ
  have hne (i : Fin N) : 1-B.eigenvalues i ≠ 0 := by
    rw [orderedBasis_values]
    exact (sub_pos.mpr (S.interval i).2).ne'
  rw [fibreSpectrum_eq_sorted S hN,spectralSorted_tsum Summable.of_finite
    (fun i => (nodeResolvent_pos S hN i).le)]
  rw [mass,Jacobi.green,SpectralCoordinates.trace_resolvent B hne,Finset.sum_div]
  simp only [B,orderedBasis_values,nodeResolvent,tsum_fintype]

end
end jacobi.Packing

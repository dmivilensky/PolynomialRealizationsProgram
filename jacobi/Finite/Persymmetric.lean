import jacobi.Finite.WeightChart
import jacobi.Finite.Reversal

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Reciprocal characteristic-derivative probabilities reconstruct the unique
persymmetric matrix in every prescribed simple-root fibre. The earlier
persymmetry criterion is reused; existence and uniqueness are discharged by
the new complete spectral-weight equivalence.
Source: de Boor and Saff, Finite sequences of orthogonal polynomials connected
by a Jacobi matrix, the reciprocal-derivative weight criterion.
Use: proves the characteristic derivatives are nonzero at all prescribed nodes.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Uniform positive probabilities, used only to realize a reference spectral basis.
Use: proves the characteristic derivatives are nonzero at all prescribed nodes.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def uniformWeights (n : ℕ) : WeightSimplex (n+1) :=
  ⟨fun _ => 1 / ((n : ℝ)+1), fun _ => by positivity,
    by simp [show (n : ℝ)+1 ≠ 0 by positivity]⟩

/-- Every derivative in the reciprocal-weight formula is nonzero.
Use: proves strict positivity of the canonical spectral probabilities.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the constructive uniform-weight reference has the distinct prescribed
spectrum, so the existing characteristic derivative theorem applies. -/
theorem Nodes.derivative_ne_zero {n : ℕ} (S : Nodes (n+1)) (k : Fin (n+1)) :
    S.polynomial.derivative.eval (S.value k) ≠ 0 := by
  let M := S.measure (uniformWeights n)
  have h := M.reconstructedBasis.charpoly_derivative_ne S.strictAnti.injective k
  rw [M.reconstructed_charpoly] at h
  exact h

/-- The positive normalization sum of reciprocal absolute characteristic derivatives.
Use: normalizes the canonical persymmetric spectral measure.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def Nodes.derivativeNormalizer {n : ℕ} (S : Nodes (n+1)) : ℝ :=
  ∑ k, |S.polynomial.derivative.eval (S.value k)|⁻¹

/-- The reciprocal-derivative normalization is strictly positive.
Use: all canonical weights and their normalizing factor have their required signs.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: every summand is positive and the node set is nonempty. -/
theorem Nodes.derivativeNormalizer_pos {n : ℕ} (S : Nodes (n+1)) :
    0 < S.derivativeNormalizer := by
  apply Finset.sum_pos
  · intro k _
    exact inv_pos.mpr (abs_pos.mpr (S.derivative_ne_zero k))
  · exact Finset.univ_nonempty

/-- The normalized reciprocal-derivative point of the open spectral simplex.
Use: reconstructs the article's canonical persymmetric matrix.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def Nodes.persymmetricWeights {n : ℕ} (S : Nodes (n+1)) : WeightSimplex (n+1) := by
  refine ⟨fun k => |S.polynomial.derivative.eval (S.value k)|⁻¹ / S.derivativeNormalizer, ?_, ?_⟩
  · intro k
    exact div_pos (inv_pos.mpr (abs_pos.mpr (S.derivative_ne_zero k))) S.derivativeNormalizer_pos
  · rw [← Finset.sum_div]
    exact div_self S.derivativeNormalizer_pos.ne'

/-- The actual canonical matrix, constructed in its prescribed polynomial fibre.
Use: is the finite candidate in the persymmetric-limit theorem.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def persymmetricFiber {n : ℕ} (S : Nodes (n+1)) : Fiber (n+1) S.polynomial :=
  reconstructFiber S S.persymmetricWeights

/-- The constructed reciprocal-weight realization is persymmetric.
Use: extends its finite spectral and diagonal identities by reversal symmetry.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the explicit reconstruction realizes the canonical weights, so the
existing inverse-spectral persymmetry criterion applies with a positive constant. -/
theorem persymmetricFiber_symmetric {n : ℕ} (S : Nodes (n+1)) :
    (persymmetricFiber S).val.matrix.submatrix Fin.rev Fin.rev = (persymmetricFiber S).val.matrix := by
  -- The reconstructed probabilities satisfy the existing reciprocal-derivative symmetry criterion.
  let M := S.measure S.persymmetricWeights
  let J := M.reconstructed
  let B := M.reconstructedBasis
  have hp : J.data.leading (n+1) = S.polynomial := by
    rw [JacobiData.leading, J.data.block_eq_charpoly J.coupling_nonneg]
    exact M.reconstructed_charpoly
  apply (J.data.persymmetric_iff_spectral_weights B J.coupling_nonneg
    M.reconstructed_irreducible S.strictAnti.injective).mpr
  refine ⟨S.derivativeNormalizer⁻¹, inv_pos.mpr S.derivativeNormalizer_pos, ?_⟩
  intro k
  have hw := M.reconstructed_weight (Nat.succ_pos n) k
  rw [hp]
  change B.weight 0 k = S.derivativeNormalizer⁻¹ / |S.polynomial.derivative.eval (S.value k)|
  calc
    B.weight 0 k = M.weight k := hw
    _ = _ := by
      change |S.polynomial.derivative.eval (S.value k)|⁻¹ / S.derivativeNormalizer = _
      ring

/-- Any persymmetric fibre element has exactly the canonical reciprocal-derivative weights.
Use: the spectral-weight equivalence then proves uniqueness of the finite candidate.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: normalize the existing proportionality criterion using total probability one. -/
theorem symmetric_weights {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial)
    (hs : J.val.matrix.submatrix Fin.rev Fin.rev = J.val.matrix) :
    spectralWeights S J = S.persymmetricWeights := by
  -- The symmetry criterion gives proportional weights; their total probability fixes the proportionality constant.
  let B := orderedBasis S J.val J.property
  have he : B.eigenvalues = S.value := orderedBasis_values S J.val J.property
  have hi : Function.Injective B.eigenvalues := he.symm ▸ S.strictAnti.injective
  have hp : J.val.data.leading (n+1) = S.polynomial := by
    rw [JacobiData.leading, J.val.data.block_eq_charpoly J.val.coupling_nonneg]
    exact J.property.2
  obtain ⟨c, hc, hw⟩ := (J.val.data.persymmetric_iff_spectral_weights B J.val.coupling_nonneg
    J.property.1 hi).mp hs
  simp only [hp, he] at hw
  have hsum := B.weight_sum 0
  simp_rw [hw, div_eq_mul_inv] at hsum
  rw [← Finset.mul_sum] at hsum
  have hcval : c = S.derivativeNormalizer⁻¹ := by
    apply mul_right_cancel₀ S.derivativeNormalizer_pos.ne'
    rw [inv_mul_cancel₀ S.derivativeNormalizer_pos.ne']
    exact hsum
  apply Subtype.ext
  funext k
  change B.weight 0 k = |S.polynomial.derivative.eval (S.value k)|⁻¹ / S.derivativeNormalizer
  rw [hw, hcval]
  ring

/-- Every simple-root fibre contains exactly one persymmetric Jacobi matrix.
Use: the finite candidate of the continuum construction is defined unambiguously.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the canonical reconstruction exists and is symmetric; all symmetric
matrices have its weights, and the proved spectral chart is injective. -/
theorem exists_unique_persymmetric {n : ℕ} (S : Nodes (n+1)) :
    ∃! J : Fiber (n+1) S.polynomial, J.val.matrix.submatrix Fin.rev Fin.rev = J.val.matrix := by
  refine ⟨persymmetricFiber S, persymmetricFiber_symmetric S, ?_⟩
  intro J hJ
  apply (weightEquiv S).injective
  exact (symmetric_weights S J hJ).trans (spectralWeights_reconstruct S S.persymmetricWeights).symm

end
end jacobi.Finite

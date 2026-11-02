import jacobi.Finite.OrderedBasis

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Every positive probability vector reconstructs a matrix in the actual fibre;
every fibre matrix is recovered from its first-site spectral probabilities.
The two inverse identities prove a genuine equivalence without postulating
reconstruction, an ordered eigenbasis, or a weight uniqueness theorem.
Source: de Boor and Golub, finite inverse spectral reconstruction.
Use: the domain of the inverse spectral chart for a fixed set of nodes.
-/

namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The positive spectral probability vectors of the article's open weight simplex.
Use: the domain of the inverse spectral chart for a fixed set of nodes.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
abbrev WeightSimplex (N : ℕ) := {w : Fin N → ℝ // (∀ i, 0 < w i) ∧ ∑ i, w i = 1}

/-- Combine the prescribed support nodes with arbitrary positive probability weights.
Use: feeds the constructive Gram--Schmidt inverse spectral map.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def Nodes.measure {N : ℕ} (S : Nodes N) (w : WeightSimplex N) : DiscreteMeasure N where
  node := S.value
  distinct := S.strictAnti.injective
  weight := w.val
  positive := w.property.1
  probability := w.property.2

/-- Every positive spectral probability vector gives an actual matrix in the fixed fibre.
Use: is the inverse direction of the article's spectral-weight chart.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def reconstructFiber {N : ℕ} (S : Nodes N) (w : WeightSimplex N) : Fiber N S.polynomial :=
  ⟨(S.measure w).reconstructed, (S.measure w).reconstructed_irreducible,
    (S.measure w).reconstructed_charpoly⟩

/-- Extract the positive first-site weights in the prescribed node order.
Use: defines the forward spectral chart on every matrix of the actual fibre.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def spectralWeights {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial) :
    WeightSimplex (n+1) := by
  let B := orderedBasis S J.val J.property
  have hi : Function.Injective B.eigenvalues := by
    rw [show B.eigenvalues = S.value from orderedBasis_values S J.val J.property]
    exact S.strictAnti.injective
  refine ⟨B.weight 0, ?_, B.weight_sum 0⟩
  intro k
  exact (J.val.data.spectral_endpoint_positive B J.val.coupling_nonneg J.property.1 hi k).1

/-- Reconstruction recovers the original fibre matrix from its extracted spectral weights.
Use: the left inverse identity in the full spectral parametrization.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: both matrices have the prescribed ordered nodes and identical first weights;
the inverse-continuant uniqueness theorem identifies their coefficient records. -/
theorem reconstruct_spectralWeights {n : ℕ} (S : Nodes (n+1))
    (J : Fiber (n+1) S.polynomial) : reconstructFiber S (spectralWeights S J) = J := by
  -- The original and reconstructed matrices have the same ordered nodes and first-site probabilities.
  apply Subtype.ext
  let B := orderedBasis S J.val J.property
  let M := S.measure (spectralWeights S J)
  have he : B.eigenvalues = M.reconstructedBasis.eigenvalues := orderedBasis_values S J.val J.property
  have hi : Function.Injective B.eigenvalues := by
    rw [he]
    exact S.strictAnti.injective
  apply (unique_of_spectral_weights J.val M.reconstructed J.property.1 B M.reconstructedBasis he hi ?_).symm
  intro k
  exact (M.reconstructed_weight (Nat.succ_pos n) k).symm

/-- Extracting weights after reconstruction recovers the input probability vector exactly.
Use: the right inverse identity, ensuring that the chart covers the entire open simplex.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the explicit reconstruction basis has the input weights, and weights at
simple fixed nodes are independent of the chosen ordered spectral basis. -/
theorem spectralWeights_reconstruct {n : ℕ} (S : Nodes (n+1)) (w : WeightSimplex (n+1)) :
    spectralWeights S (reconstructFiber S w) = w := by
  -- Compare the chosen basis with the explicit reconstruction basis at the same simple spectral nodes.
  apply Subtype.ext
  funext k
  let J := reconstructFiber S w
  let B := orderedBasis S J.val J.property
  let M := S.measure w
  have he : B.eigenvalues = M.reconstructedBasis.eigenvalues := orderedBasis_values S J.val J.property
  have hi : Function.Injective B.eigenvalues := by
    rw [he]
    exact S.strictAnti.injective
  have h := basis_weights_independent J.val B M.reconstructedBasis he hi k
  exact h.trans (M.reconstructed_weight (by omega) k)

/-- The actual irreducible arbitrary-polynomial fibre is equivalent to the open weight simplex.
Use: transports reversal and energy to spectral coordinates and constructs the persymmetric point.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def weightEquiv {n : ℕ} (S : Nodes (n+1)) : Fiber (n+1) S.polynomial ≃ WeightSimplex (n+1) where
  toFun := spectralWeights S
  invFun := reconstructFiber S
  left_inv := reconstruct_spectralWeights S
  right_inv := spectralWeights_reconstruct S

end
end jacobi.Finite

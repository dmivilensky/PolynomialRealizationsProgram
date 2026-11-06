import jacobi.Finite.Reconstruction
import jacobi.Finite.OrderedSpectrum

/-! Finite Favard existence uses the already proved positive-measure reconstruction.
Only granular dependency modules are imported; none imports the chebyshev1 root. -/
namespace chebyshev1.Background
noncomputable section
open Polynomial
open scoped BigOperators

/-- Irreducibility proves simplicity; it is not an additional spectral assumption. -/
theorem finite_jacobi_simple {N : ℕ} (J : chebyshev2.Jacobi N)
    (hJ : J.Irreducible) (B : SpectralBasis J.matrix) :
    Function.Injective B.eigenvalues :=
  jacobi.Finite.basis_values_injective J hJ B

/-- All first-site weights of an irreducible Jacobi chain are strictly positive. -/
theorem finite_jacobi_first_weights_pos {n : ℕ} (J : chebyshev2.Jacobi (n+1))
    (hJ : J.Irreducible) (B : SpectralBasis J.matrix) (j : Fin (n+1)) :
    0 < B.weight 0 j :=
  (J.data.spectral_endpoint_positive B J.coupling_nonneg hJ
    (finite_jacobi_simple J hJ B) j).1

/-- Every positive probability vector on distinct real nodes is realized by a Jacobi chain. -/
theorem finite_favard_exists {N : ℕ} (hN : 0 < N) (node weight : Fin N → ℝ)
    (hnode : Function.Injective node) (hweight : ∀ j, 0 < weight j)
    (hsum : ∑ j, weight j = 1) :
    ∃ J : JacobiData, (∀ s, 0 ≤ J.aSq s) ∧ J.aSq 0 = 0 ∧
      (∀ s, 0 < s → s < N → 0 < J.aSq s) ∧
      J.leading N = ∏ j, (X - C (node j)) ∧
      ∃ B : SpectralBasis (J.matrix 0 N),
        B.eigenvalues = node ∧ ∀ j, B.weight ⟨0, hN⟩ j = weight j := by
  let M : jacobi.Finite.DiscreteMeasure N := ⟨node, hnode, weight, hweight, hsum⟩
  refine ⟨M.reconstructed.data, M.reconstructed.coupling_nonneg,
    M.reconstructed.coupling_zero, M.reconstructed_irreducible, ?_, ?_⟩
  · rw [JacobiData.leading, M.reconstructed.data.block_eq_charpoly
      M.reconstructed.coupling_nonneg]
    exact M.reconstructed_charpoly
  · exact ⟨M.reconstructedBasis, rfl, M.reconstructed_weight hN⟩

/-- A simple first spectral measure determines every entry of an irreducible Jacobi matrix. -/
theorem finite_favard_unique {n : ℕ} (J K : JacobiData)
    (hJ : ∀ s, 0 ≤ J.aSq s) (hK : ∀ s, 0 ≤ K.aSq s)
    (hp : ∀ s, 0 < s → s < n + 1 → 0 < J.aSq s)
    (B : SpectralBasis (J.matrix 0 (n + 1)))
    (D : SpectralBasis (K.matrix 0 (n + 1)))
    (hi : Function.Injective B.eigenvalues)
    (heig : ∀ j, D.eigenvalues j = B.eigenvalues j)
    (hw : ∀ j, D.weight 0 j = B.weight 0 j) :
    J.matrix 0 (n + 1) = K.matrix 0 (n + 1) := by
  have hterminal : J.leading (n + 1) = K.leading (n + 1) := by
    change J.block 0 (n + 1) = K.block 0 (n + 1)
    rw [J.block_eq_charpoly hJ, K.block_eq_charpoly hK, B.charpoly_factor, D.charpoly_factor]
    simp only [heig]
  have hdi : Function.Injective D.eigenvalues := by
    intro j k hjk
    apply hi
    simpa only [heig] using hjk
  let M : jacobi.Finite.DiscreteMeasure (n + 1) := {
    node := B.eigenvalues
    distinct := hi
    weight := B.weight 0
    positive := fun j => (J.spectral_endpoint_positive B hJ hp hi j).1
    probability := B.weight_sum 0 }
  have htail : J.block 1 n = K.block 1 n := by
    apply M.evaluate_injective
      (by rw [J.block_natDegree hJ]; omega) (by rw [K.block_natDegree hK]; omega)
    apply PiLp.ext
    intro j
    have hj := J.spectral_weight_cofactor B hJ hi 0 j
    have hk := K.spectral_weight_cofactor D hK hdi 0 j
    simp only [Fin.val_zero, JacobiData.leading_zero, eval_one, one_mul,
      Nat.zero_add, Nat.sub_zero] at hj hk
    rw [← hterminal, heig, hw] at hk
    change Real.sqrt (B.weight 0 j) * (J.block 1 n).eval (B.eigenvalues j) =
      Real.sqrt (B.weight 0 j) * (K.block 1 n).eval (B.eigenvalues j)
    rw [hj.symm.trans hk]
  have hc := J.block_pair_unique K hJ hK n 0 0
    (fun s hs hsN => by simpa using hp s hs (by omega)) hterminal htail
  simp only [Nat.zero_add] at hc
  ext i j
  simp only [JacobiData.matrix_apply, Nat.zero_add]
  split_ifs with hij hu hl
  · exact hc.1 i.val (by omega)
  · rw [hc.2 j.val (by omega) (by omega)]
  · rw [hc.2 i.val (by omega) (by omega)]
  · rfl

end
end chebyshev1.Background

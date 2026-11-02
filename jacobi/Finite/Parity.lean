import jacobi.Finite.Endpoint

/-!
Article: jacobi, Proposition C.3.
Descending simple nodes determine the alternating sign of the characteristic
derivative. The signed endpoint residue then determines the action of physical
reversal on every component of every persymmetric eigenvector.
Source: finite Jacobi cofactor theory and the product formula for p′ at simple roots.
Use: fixes the eigenvector parity, with zero-based indices corresponding to k-1 in print.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The characteristic derivative at the k-th descending node has sign (-1)^k.
Use: fixes the eigenvector parity, with zero-based indices corresponding to k-1 in print.
Article: jacobi, Proposition C.3.
Proof: exactly k factors in the simple-root derivative product are negative. -/
theorem Nodes.derivative_sign {n : ℕ} (S : Nodes (n+1)) (k : Fin (n+1)) :
    0 < (-1 : ℝ)^k.val * S.polynomial.derivative.eval (S.value k) := by
  -- Split the simple-root derivative product into the k negative factors and the positive remaining factors.
  let M := S.measure (uniformWeights n)
  have hd := M.reconstructedBasis.charpoly_derivative k
  rw [M.reconstructed_charpoly] at hd
  change S.polynomial.derivative.eval (S.value k) =
    ∏ j ∈ Finset.univ.erase k, (S.value k-S.value j) at hd
  have he : Finset.univ.erase k = Finset.Iio k ∪ Finset.Ioi k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    exact ne_iff_lt_or_gt
  have hdis : Disjoint (Finset.Iio k) (Finset.Ioi k) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact (lt_trans (Finset.mem_Iio.mp hj) (Finset.mem_Ioi.mp hj')).false
  have hleft : (∏ j ∈ Finset.Iio k, (S.value k-S.value j)) =
      (-1 : ℝ)^k.val * ∏ j ∈ Finset.Iio k, (S.value j-S.value k) := by
    simp_rw [show ∀ j, S.value k-S.value j = -(S.value j-S.value k) by intro j; ring]
    rw [Finset.prod_neg, Fin.card_Iio]
  have hpos : 0 < (∏ j ∈ Finset.Iio k, (S.value j-S.value k)) *
      ∏ j ∈ Finset.Ioi k, (S.value k-S.value j) := by
    apply mul_pos <;> apply Finset.prod_pos
    · intro j hj
      exact sub_pos.mpr (S.strictAnti (Finset.mem_Iio.mp hj))
    · intro j hj
      exact sub_pos.mpr (S.strictAnti (Finset.mem_Ioi.mp hj))
  rw [hd, he, Finset.prod_union hdis, hleft]
  have hs : (-1 : ℝ)^k.val * (-1)^k.val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  simpa only [← mul_assoc, hs, one_mul] using hpos

/-- A persymmetric matrix has a reversal-invariant spectral rank-one projector.
Use: propagates the endpoint parity sign to every physical coordinate.
Article: jacobi, Proposition C.3.
Proof: adjugates commute with simultaneous coordinate permutations; dividing
by the nonzero characteristic derivative yields equality of projector entries. -/
theorem projector_reversal {n : ℕ} (J : Jacobi (n+1)) (B : SpectralBasis J.matrix)
    (hi : Function.Injective B.eigenvalues)
    (hs : J.matrix.submatrix Fin.rev Fin.rev = J.matrix) (i l k : Fin (n+1)) :
    B.Q i.rev k * B.Q l.rev k = B.Q i k * B.Q l k := by
  -- Apply reversal to the adjugate, then cancel its nonzero spectral derivative factor.
  let A := Matrix.scalar (Fin (n+1)) (B.eigenvalues k)-J.matrix
  have ha : A.submatrix Fin.rev Fin.rev = A := by
    change (Matrix.scalar _ _).submatrix Fin.rev Fin.rev -
      J.matrix.submatrix Fin.rev Fin.rev = _
    rw [hs]
    congr 1
    ext u v
    change (if u.rev = v.rev then B.eigenvalues k else 0) =
      (if u = v then B.eigenvalues k else 0)
    simp only [Fin.rev_injective.eq_iff]
  have h := Matrix.adjugate_submatrix_equiv_self Fin.revPerm A
  change (A.submatrix Fin.rev Fin.rev).adjugate = A.adjugate.submatrix Fin.rev Fin.rev at h
  rw [ha] at h
  have he := congrArg (fun C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => C i l) h
  change A.adjugate i l = A.adjugate i.rev l.rev at he
  apply mul_right_cancel₀ (B.charpoly_derivative_ne hi k)
  calc
    _ = A.adjugate i.rev l.rev := (adjugate_eigenvalue_entry B i.rev l.rev k).symm
    _ = A.adjugate i l := he.symm
    _ = _ := adjugate_eigenvalue_entry B i l k

/-- All components of every ordered persymmetric eigenvector have the stated parity.
Use: extends finite half-chain limits to the full interval in the persymmetric limit theorem.
Article: jacobi, Proposition C.3.
Proof: reversal invariance of the spectral projector gives equal endpoint squares;
the positive signed endpoint residue and the derivative sign select the correct
endpoint sign, which the same projector identity propagates to every component. -/
theorem eigenvector_parity {n : ℕ} (S : Nodes (n+1)) (J : Fiber (n+1) S.polynomial)
    (B : SpectralBasis J.val.matrix) (he : B.eigenvalues = S.value)
    (hs : J.val.matrix.submatrix Fin.rev Fin.rev = J.val.matrix) (i k : Fin (n+1)) :
    B.Q i.rev k = (-1 : ℝ)^k.val * B.Q i k := by
  -- The signed endpoint cofactor selects the endpoint sign; projector invariance propagates it to every entry.
  have hi : Function.Injective B.eigenvalues := he.symm ▸ S.strictAnti.injective
  have hx : B.Q 0 k ≠ 0 := by
    have h := (J.val.data.spectral_endpoint_positive B J.val.coupling_nonneg J.property.1 hi k).1
    intro hz
    simp only [SpectralBasis.weight, hz, zero_pow (by decide : 2 ≠ 0)] at h
    exact lt_irrefl 0 h
  have hw := projector_reversal J.val B hi hs 0 0 k
  simp only [Fin.rev_zero] at hw
  have hp := spectral_endpoint_signed J.val B k
  rw [J.property.2, he] at hp
  have hpp : 0 < ∏ j : Fin n, Real.sqrt (J.val.data.aSq (j.val+1)) := by
    apply Finset.prod_pos
    intro j _
    exact Real.sqrt_pos.mpr (J.property.1 _ (by omega) (by have := j.isLt; omega))
  have hd := S.derivative_sign k
  have hsign : ((-1 : ℝ)^k.val)^2 = 1 := by rw [← pow_mul, mul_comm k.val 2, pow_mul]; simp
  have hlast : B.Q (Fin.last n) k = (-1 : ℝ)^k.val * B.Q 0 k := by
    rcases sq_eq_one_iff.mp hsign with h | h
    · rw [h] at hd ⊢
      rcases mul_self_eq_mul_self_iff.mp hw with hq | hq
      · simp [hq]
      · rw [hq] at hp
        have hm := mul_nonneg (sq_nonneg (B.Q 0 k)) (by linarith :
          0 ≤ S.polynomial.derivative.eval (S.value k))
        nlinarith [hm]
    · rw [h] at hd ⊢
      rcases mul_self_eq_mul_self_iff.mp hw with hq | hq
      · rw [hq] at hp
        have hm := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (B.Q 0 k)) (by linarith :
          S.polynomial.derivative.eval (S.value k) ≤ 0)
        nlinarith [hm]
      · simp [hq]
  have h := projector_reversal J.val B hi hs i 0 k
  simp only [Fin.rev_zero, hlast] at h
  have h' := mul_right_cancel₀ hx (show
      (B.Q i.rev k * (-1 : ℝ)^k.val) * B.Q 0 k = B.Q i k * B.Q 0 k by nlinarith [h])
  have hh := congrArg (fun x : ℝ => x * (-1 : ℝ)^k.val) h'
  simpa only [mul_assoc, ← pow_two, hsign, mul_one] using hh.trans (mul_comm _ _)

end
end jacobi.Finite

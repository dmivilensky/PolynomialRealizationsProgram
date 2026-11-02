import jacobi.Support.Chain

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Exact original finite matrix entries connect the existing Jacobi encoding
to the genuine support coefficients. The Darboux and affine-support
arguments reuse these diagonal, adjacent and zero-band identities.
Use: both genuine Darboux Gram diagonals are identified with the unchanged original finite support matrices.
-/
namespace jacobi.Support
noncomputable section
open Real chebyshev2 chebyshev1

/-- Every actual natural support matrix diagonal is the original printed b_m.
Use: both genuine Darboux Gram diagonals are identified with the unchanged original finite support matrices.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: evaluate the existing Jacobi matrix diagonal and its proved actual finite coefficient. -/
theorem naturalChain_matrix_diagonal (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ} (i:Fin n) :
    (naturalChain a b ha hb n).matrix i i=diagonal a b n i := by
  simp only [Jacobi.matrix,JacobiData.matrix_apply,ite_true,Nat.zero_add]
  exact naturalChain_diagonal a b ha hb i.isLt

/-- Every actual natural support upper adjacent matrix entry is the original positive square-root coupling.
Use: the rectangular Darboux products identify the exact same symmetric original couplings.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: evaluate the existing upper adjacent Jacobi matrix entry and the genuine squared coefficient; the actual neighboring indices agree. -/
theorem naturalChain_matrix_upper (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ}
    (i j:Fin n) (hij:(i:ℕ)+1=(j:ℕ)) :
    (naturalChain a b ha hb n).matrix i j=
      Real.sqrt (coefficientA a b n i*coefficientC a b n ((i:ℕ)+1)/4) := by
  have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
  simp only [Jacobi.matrix,JacobiData.matrix_apply,Nat.zero_add,ite_eq_right hne,ite_eq_left hij]
  rw [naturalChain_coupling a b ha hb (by omega : 0<(j:ℕ)) j.isLt]
  rw [← hij,Nat.add_sub_cancel]

/-- Every actual natural support matrix entry beyond the original tridiagonal band is zero.
Use: full Darboux and affine matrix identities compare every remaining actual original entry.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: distinct nonadjacent original finite indices select the existing Jacobi encoding's genuine zero branch. -/
theorem naturalChain_matrix_far (a b : ℝ) (ha : -1<a) (hb : -1<b) {n : ℕ}
    (i j:Fin n) (hij:(i:ℕ)+1<(j:ℕ) ∨ (j:ℕ)+1<(i:ℕ)) :
    (naturalChain a b ha hb n).matrix i j=0 := by
  have hne : i≠j := by intro h; have := congrArg Fin.val h; omega
  simp only [Jacobi.matrix,JacobiData.matrix_apply,ite_eq_right hne,
    ite_eq_right (by omega : ¬(i:ℕ)+1=(j:ℕ)),ite_eq_right (by omega : ¬(j:ℕ)+1=(i:ℕ))]

end
end jacobi.Support

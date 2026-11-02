import jacobi.Support.Bidiagonal

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Both actual rectangular Darboux Gram matrices are tridiagonal. Their
diagonals and neighboring entries retain their genuine finite endpoint
terms. These elementary identities identify the actual support chain
and its endpoint-deleted parameter shift without a spectral premise.
Use: supportDarboux_original cancels the genuine boundary-zero factors and identifies the entire original support matrix.
-/
namespace jacobi.Support
noncomputable section
open Matrix Finset

/-- The larger actual bidiagonal Gram diagonal retains exactly the available original column contributions.
Use: supportDarboux_original cancels the genuine boundary-zero factors and identifies the entire original support matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: evaluate the actual two-term column formula; at each available index its genuine column value is respectively p_j and -q_(j-1). -/
theorem bidiagonal_columns_diagonal (n : ℕ) (p q : ℕ → ℝ) (j : Fin (n+1)) :
    ((bidiagonal n p q).transpose*bidiagonal n p q) j j=
      (if (j:ℕ)<n then (p j)^2 else 0)+(if 0<(j:ℕ) then (q ((j:ℕ)-1))^2 else 0) := by
  -- The finite boundary branches are kept until the actual factor values have been evaluated.
  rw [mul_apply]
  change (∑ i:Fin n,bidiagonal n p q i j*bidiagonal n p q i j)=_
  rw [bidiagonal_column_sum]
  have hA (hj:(j:ℕ)<n) : bidiagonal n p q ⟨j,hj⟩ j=p j := by
    have h0 : j=(⟨j,hj⟩:Fin n).castSucc := Fin.ext rfl
    have h1 : j≠(⟨j,hj⟩:Fin n).succ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    simp only [bidiagonal,ite_eq_left h0,ite_eq_right h1,sub_zero]
  have hB (hj:0<(j:ℕ)) : bidiagonal n p q ⟨(j:ℕ)-1,by omega⟩ j= -q ((j:ℕ)-1) := by
    have h0 : j≠(⟨(j:ℕ)-1,by omega⟩:Fin n).castSucc := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    have h1 : j=(⟨(j:ℕ)-1,by omega⟩:Fin n).succ := Fin.ext (by dsimp; omega)
    simp only [bidiagonal,ite_eq_right h0,ite_eq_left h1,zero_sub]
  split_ifs <;> simp only [hA,pow_two,sub_zero,add_zero,zero_sub]
  all_goals (rw [hB (by assumption)]; ring)

/-- The larger actual bidiagonal Gram upper adjacent entry is exactly minus the original shared p_i*q_i factor.
Use: supportDarboux_original recovers the actual original positive square-root support coupling with its correct sign.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the actual adjacent columns have exactly one original common row; its two factors have opposite signs. -/
theorem bidiagonal_columns_upper (n : ℕ) (p q : ℕ → ℝ) (i j : Fin (n+1)) (hij : (i:ℕ)+1=j) :
    ((bidiagonal n p q).transpose*bidiagonal n p q) i j= -p i*q i := by
  -- Evaluate the genuine finite-column sum at the actual adjacent pair; every other overlap is excluded by its natural indices.
  rw [mul_apply]
  change (∑ k:Fin n,bidiagonal n p q k i*bidiagonal n p q k j)=_
  rw [bidiagonal_column_sum]
  have hi : (i:ℕ)<n := by omega
  rw [dite_eq_left hi]
  simp only [bidiagonal,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  split_ifs <;> first | omega | ring

/-- The smaller genuine bidiagonal Gram has zero entries beyond its two original neighboring diagonals.
Use: supportDarboux_shifted identifies all remaining entries of the smaller original support matrix.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the two original row supports are disjoint at this actual distance, so every genuine matrix-product summand vanishes. -/
theorem bidiagonal_rows_far (n : ℕ) (p q : ℕ → ℝ) (i j : Fin n)
    (hij : (i:ℕ)+1<(j:ℕ) ∨ (j:ℕ)+1<(i:ℕ)) :
    (bidiagonal n p q*(bidiagonal n p q).transpose) i j=0 := by
  rw [mul_apply]
  apply sum_eq_zero
  intro k _
  simp only [transpose_apply,bidiagonal,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  split_ifs <;> first | omega | ring

/-- The larger genuine bidiagonal Gram has zero entries outside its actual original tridiagonal band.
Use: supportDarboux_original identifies the complete finite factorization, rather than only its diagonal and adjacent entries.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the two genuine physical column supports cannot overlap at this actual index distance, so every finite product summand is zero. -/
theorem bidiagonal_columns_far (n : ℕ) (p q : ℕ → ℝ) (i j : Fin (n+1))
    (hij : (i:ℕ)+1<(j:ℕ) ∨ (j:ℕ)+1<(i:ℕ)) :
    ((bidiagonal n p q).transpose*bidiagonal n p q) i j=0 := by
  rw [mul_apply]
  apply sum_eq_zero
  intro k _
  simp only [transpose_apply,bidiagonal,Fin.ext_iff,Fin.val_castSucc,Fin.val_succ]
  split_ifs <;> first | omega | ring

end
end jacobi.Support

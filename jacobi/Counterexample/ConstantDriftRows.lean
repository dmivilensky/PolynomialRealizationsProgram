import jacobi.Counterexample.BidiagonalInverse

/-!
Article: jacobi, Section 6 (bidiagonal swap identity).
The actual inverse row norms satisfy the printed scalar recursion.
Constant diagonal-minus-subdiagonal squared drift makes every genuine
row norm exactly 1/kappa. No row-norm or inverse-diagonal certificate is
an additional hypothesis of these statements.
Use: row_norm_constant and swapped_inverse_diagonal compute the diagonal of the actual swapped matrix inverse.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine squared norm of an explicit original inverse row on the full finite column interval.
Use: row_norm_constant and swapped_inverse_diagonal compute the diagonal of the actual swapped matrix inverse.
Article: jacobi, Section 6 (bidiagonal swap identity).
-/
def inverseRowNorm (d l:ℕ→ℝ) (N i:ℕ) : ℝ :=
  ∑j:Fin N,(inverseEntry d l i j)^2

/-- The original zeroth inverse row has exactly the source's initial squared norm.
Use: row_norm_constant starts the actual constant-drift induction with r_0=1/A_0.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the true forward-substitution zeroth row has only its original zeroth coordinate. -/
theorem row_norm_zero {N:ℕ} (hN:0<N) (d l:ℕ→ℝ) :
    inverseRowNorm d l N 0=1/(d 0)^2 := by
  classical
  have he (j:Fin N) : j.val=0 ↔ j=⟨0,hN⟩ := by
    constructor
    · intro h; apply Fin.ext; exact h
    · exact congrArg Fin.val
  simp only [inverseRowNorm,inverseEntry,he,ite_div,zero_div,ite_pow,zero_pow (by norm_num : (2:ℕ)≠0)]
  simp

/-- Every actual next inverse row satisfies the exact original squared-row recursion.
Use: row_norm_constant proves the original swapped inverse diagonal without assuming its value.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: square the true forward-substitution row. Its old row is zero
at the new diagonal coordinate, so the mixed term vanishes exactly.
Sum the new singleton coordinate and the unchanged preceding row square. -/
theorem row_norm_succ {N i:ℕ} (hi:i+1<N) (d l:ℕ→ℝ) :
    inverseRowNorm d l N (i+1)=
      (1+(l (i+1))^2*inverseRowNorm d l N i)/(d (i+1))^2 := by
  classical
  -- The actual triangular support supplies orthogonality to the new physical coordinate.
  have he (j:Fin N) : (inverseEntry d l (i+1) j)^2=
      (if j.val=i+1 then 1 else 0)/(d (i+1))^2+
        ((l (i+1))^2/(d (i+1))^2)*(inverseEntry d l i j)^2 := by
    rw [inverseEntry]
    by_cases hj:j.val=i+1
    · rw [ite_eq_left hj,inverseEntry_support d l (by omega : i<j.val)]
      ring
    · rw [ite_eq_right hj]
      ring
  have hj (j:Fin N) : j.val=i+1 ↔ j=⟨i+1,hi⟩ := by
    constructor
    · intro h; apply Fin.ext; exact h
    · exact congrArg Fin.val
  simp only [inverseRowNorm,he,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [hj,ite_div,zero_div,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

/-- Under the source's constant positive drift, all genuine inverse row norms equal 1/kappa.
Use: swapped_inverse_diagonal gives the original constant Green diagonal, hence exact attainment of the complete finite-fibre energy lower bound.
Article: jacobi, Section 6 (bidiagonal swap identity).
Proof: the unused first lower coefficient is zero, so d_0^2=kappa.
In every later genuine row the proved recurrence becomes
(1+l_i^2/kappa)/d_i^2=1/kappa because d_i^2-l_i^2=kappa. -/
theorem row_norm_constant {N:ℕ} (d l:ℕ→ℝ) {kappa:ℝ}
    (hk:0<kappa) (hl:l 0=0) (hd:∀i<N,(d i)^2-(l i)^2=kappa)
    {i:ℕ} (hi:i<N) : inverseRowNorm d l N i=1/kappa := by
  -- This induction concerns every actual finite row, including the original zeroth row.
  induction i with
  | zero =>
    have h0 := hd 0 hi
    rw [hl] at h0
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at h0
    rw [row_norm_zero (by omega) d l,h0]
  | succ i ih =>
    rw [row_norm_succ hi d l,ih (by omega)]
    have hrow := hd (i+1) hi
    have hnon : (d (i+1))^2≠0 := by nlinarith [sq_nonneg (l (i+1))]
    rw [div_eq_iff hnon]
    field_simp [hk.ne']
    nlinarith

end
end jacobi.Counterexample

import krylov.Strings.DiscreteInverseSpectral

/-!
Article: `main_krylov`, `apC:lem:stieltjes(b)`.
Exact source formulas for the inverse masses, gaps and Robin boundary.
The true terminal polynomial is a positively normalized full Jacobi
characteristic polynomial, so the free terminal boundary is equivalent
to an actual atom at zero in the prescribed input spectral measure.
-/

namespace krylov.Strings.DiscreteInverse
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (M : DiscreteMeasure (N+1))

/-- The terminal polynomial with the canonical last-polynomial normalization. -/
def terminalPolynomial : ℝ[X] :=
  C (M.reconstructed.data.linkProduct N)⁻¹*M.reconstructed.data.leading (N+1)

/-- The genuine terminal polynomial has exactly the source's last-row
three-term formula, including the one-atom boundary case. -/
theorem terminalPolynomial_formula :
    terminalPolynomial M=(X-C (M.reconstructed.data.b N))*
      M.orthogonalPolynomial ⟨N,by omega⟩-
      (if h : 0<N then C (coupling M (N-1))*M.orthogonalPolynomial ⟨N-1,by omega⟩ else 0) := by
  cases N with
  | zero =>
    rw [terminalPolynomial, JacobiData.linkProduct_zero]
    simp only [inv_one, C_1, one_mul, Nat.lt_irrefl, dite_false, sub_zero]
    rw [krylov.Reference.orthogonalPolynomial_first]
    simpa only [Nat.zero_add, mul_one] using M.reconstructed.data.leading_one
  | succ n =>
    rw [dite_eq_left (Nat.succ_pos n)]
    have h0 := linkProduct_pos M.reconstructed_irreducible (show n<n+1+1 by omega)
    have h1 := linkProduct_pos M.reconstructed_irreducible (show n+1<n+1+1 by omega)
    have hc := Real.sqrt_pos.mpr (M.reconstructed_irreducible (n+1) (by omega) (by omega))
    have hrec := M.reconstructed.data.leading_add_two n
    apply Polynomial.funext
    intro z
    rw [terminalPolynomial, hrec]
    simp only [Nat.add_sub_cancel]
    rw [← normalizedLeading_eq_orthogonalPolynomial M ⟨n+1,by omega⟩,
      ← normalizedLeading_eq_orthogonalPolynomial M ⟨n,by omega⟩]
    simp only [normalizedLeading, eval_mul, eval_sub, eval_X, eval_C, coupling,
      JacobiData.linkProduct_succ]
    field_simp
    rw [Real.sq_sqrt (M.reconstructed.coupling_nonneg (n+1))]

/-- Inverse source mass formula, with the actual canonical polynomial at zero. -/
theorem mass_formula (hnode : ∀ i,0≤M.node i) (i : Fin (N+1)) :
    (string M hnode).mass i.val=((M.orthogonalPolynomial i).eval 0)^2 := by
  rw [string_mass, zeroValue, dite_eq_left i.isLt, mul_pow, alternating_sq, one_mul]

/-- Inverse source positive-gap formula with the genuine Jacobi coupling. -/
theorem gap_formula (hnode : ∀ i,0≤M.node i) (k : ℕ) (hk : k<N) :
    (string M hnode).gap k=
      -1/(coupling M k*(M.orthogonalPolynomial ⟨k,by omega⟩).eval 0*
        (M.orthogonalPolynomial ⟨k+1,by omega⟩).eval 0) := by
  have hprod : zeroValue M k*zeroValue M (k+1)=
      -(M.orthogonalPolynomial ⟨k,by omega⟩).eval 0*
        (M.orthogonalPolynomial ⟨k+1,by omega⟩).eval 0 := by
    rw [zeroValue, dite_eq_left (by omega : k<N+1), zeroValue,
      dite_eq_left (by omega : k+1<N+1), pow_succ]
    have hs := alternating_sq k
    linear_combination -(M.orthogonalPolynomial ⟨k,by omega⟩).eval 0*
      (M.orthogonalPolynomial ⟨k+1,by omega⟩).eval 0*hs
  rw [string_gap, mul_assoc, hprod]
  simp only [← mul_assoc, mul_neg, neg_mul, inv_neg, neg_div, one_div]

/-- The actual inverse Robin coefficient is the exact signed canonical
terminal-polynomial expression displayed in the source. -/
theorem robin_formula :
    robin M=-(M.orthogonalPolynomial ⟨N,by omega⟩).eval 0*(terminalPolynomial M).eval 0 := by
  rw [terminalPolynomial_formula]
  have hv (k : ℕ) (hk : k<N+1) :
      (M.orthogonalPolynomial ⟨k,hk⟩).eval 0=(-1 : ℝ)^k*zeroValue M k := by
    rw [zeroValue, dite_eq_left hk]
    have hs := alternating_sq k
    linear_combination -(M.orthogonalPolynomial ⟨k,hk⟩).eval 0*hs
  simp only [eval_sub, eval_mul, eval_X, eval_C, zero_sub, robin]
  rw [hv N (by omega)]
  have hs := alternating_sq N
  by_cases hN : 0<N
  · rw [dite_eq_left hN, ite_eq_left hN, eval_mul, eval_C, hv (N-1) (by omega)]
    have he : N-1+1=N := by omega
    have hs' : (-1 : ℝ)^(N-1)=-(-1 : ℝ)^N := by
      have ht : (-1 : ℝ)^N=(-1 : ℝ)^(N-1)*(-1) := by
        conv_lhs => rw [← he]
        exact pow_succ _ _
      linear_combination ht
    rw [hs']
    linear_combination -(M.reconstructed.data.b N*zeroValue M N^2-
      coupling M (N-1)*zeroValue M (N-1)*zeroValue M N)*hs
  · rw [dite_eq_right hN, ite_eq_right hN, eval_zero, sub_zero]
    linear_combination -(M.reconstructed.data.b N*zeroValue M N^2)*hs

/-- Free terminal boundary is equivalent to an actual prescribed zero
spectral atom; all sign and normalization conditions have been discharged. -/
theorem robin_eq_zero_iff (hnode : ∀ i,0≤M.node i) :
    (string M hnode).robin=0 ↔ ∃ i,M.node i=0 := by
  have hq : (M.orthogonalPolynomial ⟨N,by omega⟩).eval 0≠0 := by
    have h := (zeroValue_pos M hnode N).ne'
    rw [zeroValue, dite_eq_left (show N<N+1 by omega)] at h
    exact (mul_ne_zero_iff.mp h).2
  have hl := (linkProduct_pos M.reconstructed_irreducible (show N<N+1 by omega)).ne'
  rw [string_robin, robin_formula, mul_eq_zero]
  simp only [neg_eq_zero, hq, false_or]
  rw [terminalPolynomial, eval_mul, eval_C, mul_eq_zero]
  simp only [inv_eq_zero, hl, false_or]
  rw [JacobiData.leading,
    M.reconstructed.data.block_eq_charpoly M.reconstructed.coupling_nonneg]
  change M.reconstructed.matrix.charpoly.eval 0=0 ↔ _
  rw [M.reconstructed_charpoly]
  simp only [eval_prod, eval_sub, eval_X, eval_C, zero_sub, Finset.prod_eq_zero_iff,
    Finset.mem_univ, neg_eq_zero, true_and]

end
end krylov.Strings.DiscreteInverse

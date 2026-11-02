import krylov.Strings.DiscreteTopTerminal
import krylov.Strings.DiscreteInverseBoundary

/-!
Article: `main_krylov`, `apC:prop:local`.
Complete the exact top-solution equivalence. The actual terminal residual
is identified with the full shifted determinant, including its genuine
mass and Jacobi product factors. Positivity of the actual top positions
and this residual therefore gives the real shifted form by the existing
Sylvester theorem, and hence the strict physical spectral norm bound.
-/

/-!
Article: krylov, Proposition D.17 [apC:prop:local].

Positivity of the top positions/fluxes and the terminal Robin inequality is equivalent to the
actual physical operator norm bound.
The terminal flux is the physical topTerminal expression; no top-positivity certificate is
assumed for the converse.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- Exact physical diagonal of the actual positive Jacobi orientation. -/
theorem jacobi_diagonal_physical (i : Fin (N+1)) :
    S.jacobi.data.b i.val=S.operator i i := by
  have he := congrArg (fun A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ ↦ A i i) S.jacobi_matrix
  simp only [Jacobi.matrix, JacobiData.matrix_apply, ite_true, Nat.zero_add,
    positiveOperator_apply] at he
  have hs := alternating_sq i.val
  linear_combination he+S.operator i i*hs

/-- Exact physical adjacent coupling in the genuine Jacobi coefficient
normalization used in the continuant determinant. -/
theorem jacobi_coupling_physical (i j : Fin (N+1)) (hij : i.val+1=j.val) :
    Real.sqrt (S.jacobi.data.aSq j.val)=
      (S.gap i.val)⁻¹*(Real.sqrt (S.mass i.val))⁻¹*(Real.sqrt (S.mass j.val))⁻¹ := by
  have he := congrArg (fun A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ ↦ A i j) S.jacobi_matrix
  have hne : i≠j := by intro h; subst j; omega
  simp only [Jacobi.matrix, JacobiData.matrix_apply, ite_eq_right hne,
    ite_eq_left hij, Nat.zero_add] at he
  rw [S.positiveOperator_adjacent i j hij, S.operator_adjacent i j hij] at he
  linear_combination he

/-- The full actual terminal residual is its true determinant with exactly
the source's positive normalization; no sign is postulated at the boundary. -/
theorem topTerminal_determinant (Λ : ℝ) (hN : 0<N) :
    S.topTerminal Λ=Real.sqrt (S.mass N)*(S.jacobi.data.linkProduct N)⁻¹*
      (S.jacobi.data.leading (N+1)).eval Λ := by
  let M := S.spectralData
  let last : Fin (N+1) := ⟨N,by omega⟩
  let prev : Fin (N+1) := ⟨N-1,by omega⟩
  have hJ : M.reconstructed=S.jacobi := S.spectralData_reconstructed
  have hpoly (k : ℕ) (hk : k≤N) :
      (M.orthogonalPolynomial ⟨k,by omega⟩).eval Λ=Real.sqrt (S.mass k)*S.topA Λ k := by
    rw [S.orthogonalPolynomial_eq]
    simp only [eval_mul, eval_C, topA]
    ring
  have ht := congrArg (fun P : ℝ[X] ↦ P.eval Λ) (DiscreteInverse.terminalPolynomial_formula M)
  rw [dite_eq_left hN, eval_sub, eval_mul, eval_sub, eval_X, eval_C,
    eval_mul, eval_C, hpoly N le_rfl, hpoly (N-1) (by omega)] at ht
  have hd := S.operator_diagonal last
  simp only [last, lt_irrefl, ite_false, hN, ite_true, zero_add] at hd
  have hb : M.reconstructed.data.b N=
      (S.gap (N-1))⁻¹*(S.mass N)⁻¹+S.robin*(S.mass N)⁻¹ := by
    rw [hJ]
    exact (S.jacobi_diagonal_physical last).trans hd
  have hc : DiscreteInverse.coupling M (N-1)=
      (S.gap (N-1))⁻¹*(Real.sqrt (S.mass (N-1)))⁻¹*(Real.sqrt (S.mass N))⁻¹ := by
    rw [DiscreteInverse.coupling, hJ, Nat.sub_add_cancel (by omega)]
    exact S.jacobi_coupling_physical prev last (by change N-1+1=N; omega)
  rw [hb, hc] at ht
  have hg := (S.gap_pos (N-1) (by omega)).ne'
  have hm := S.mass_pos N le_rfl
  have hp := S.mass_pos (N-1) (by omega)
  have hsm := (Real.sqrt_pos.mpr hm).ne'
  have hsp := (Real.sqrt_pos.mpr hp).ne'
  have ha := S.topA_succ Λ (N-1)
  rw [Nat.sub_add_cancel (by omega)] at ha
  have he : S.topTerminal Λ=Real.sqrt (S.mass N)*(DiscreteInverse.terminalPolynomial M).eval Λ := by
    rw [ht, topTerminal]
    field_simp
    rw [Real.sq_sqrt hm.le]
    linear_combination S.mass N*ha
  rw [he, DiscreteInverse.terminalPolynomial, eval_mul, eval_C, hJ]
  ring

/-- Exact leading shifted determinant, including all actual finite coordinate
inclusions, with no positivity hypothesis on the upper parameter. -/
theorem shifted_leading_determinant (Λ : ℝ) (k : ℕ) (hk : k≤N+1) :
    (krylov.LinearAlgebra.leadingBlock
      (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix) k hk).det=
      (S.jacobi.data.leading k).eval Λ := by
  let e : Fin k→Fin (N+1) := fun i ↦ ⟨0+i.val,by omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    simpa only [e, Nat.zero_add] using congrArg Fin.val h
  have hsub : krylov.LinearAlgebra.leadingBlock
      (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix) k hk=
      Λ • 1-S.jacobi.data.matrix 0 k := by
    have hi : krylov.LinearAlgebra.leadingBlock
        (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix) k hk=
        (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix).submatrix e e := by
      ext i j
      change (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix)
        (Fin.castLE hk i) (Fin.castLE hk j)=
        (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix) (e i) (e j)
      exact congrArg₂
        (fun a b : Fin (N+1) ↦
          (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix) a b)
        (by apply Fin.ext; simp [e]) (by apply Fin.ext; simp [e])
    rw [hi]
    change (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)).submatrix e e-
      (S.jacobi.data.matrix 0 (N+1)).submatrix e e=_
    rw [S.jacobi.data.matrix_principal_block (N+1) 0 k (by omega)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, he.eq_iff]
  rw [hsub, JacobiData.leading,
    S.jacobi.data.block_eq_charpoly S.jacobi.coupling_nonneg, Matrix.eval_charpoly]
  congr 1
  ext i j
  by_cases hij : i=j <;> simp [Matrix.scalar, hij]

/-- Actual top positivity and actual terminal positivity imply the genuine
strict physical spectral norm bound, completing the converse direction. -/
theorem spectralRadius_lt_of_top {Λ : ℝ} (hN : 0<N)
    (ha : ∀ k≤N,0<S.topA Λ k) (ht : 0<S.topTerminal Λ) : S.spectralRadius<Λ := by
  have hleading (k : ℕ) (hk : k≤N+1) : 0<(S.jacobi.data.leading k).eval Λ := by
    by_cases hkN : k≤N
    · have hn := congrArg (fun P : ℝ[X] ↦ P.eval Λ)
        (S.normalizedLeading_physical ⟨k,by omega⟩)
      have hp := linkProduct_pos S.jacobi_irreducible (show k<N+1 by omega)
      have hm := Real.sqrt_pos.mpr (S.mass_pos k hkN)
      have he : (S.jacobi.data.linkProduct k)⁻¹*(S.jacobi.data.leading k).eval Λ=
          Real.sqrt (S.mass k)*S.topA Λ k := by
        simpa only [normalizedLeading, eval_mul, eval_C, topA, mul_assoc, mul_left_comm] using hn
      have hh : 0<(S.jacobi.data.linkProduct k)⁻¹*(S.jacobi.data.leading k).eval Λ :=
        he.symm ▸ mul_pos hm (ha k hkN)
      exact pos_of_mul_pos_right hh (inv_pos.mpr hp).le
    · have he : k=N+1 := by omega
      rw [he]
      rw [S.topTerminal_determinant Λ hN] at ht
      exact pos_of_mul_pos_right ht
        (mul_pos (Real.sqrt_pos.mpr (S.mass_pos N le_rfl))
          (inv_pos.mpr (linkProduct_pos S.jacobi_irreducible (show N<N+1 by omega)))).le
  have hZ : (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.jacobi.matrix).PosDef := by
    apply krylov.LinearAlgebra.posDef_of_leading_determinants
    · have hs : (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)).IsHermitian := by
        simp [Matrix.IsHermitian]
      exact hs.sub S.jacobi.matrix_isHermitian
    · intro k _ hk
      rw [S.shifted_leading_determinant]
      exact hleading k hk
  have hc := (krylov.LinearAlgebra.coordinates_posDef_iff S.positiveBasis _).2 hZ
  rw [krylov.LinearAlgebra.coordinates_upper_shift, Matrix.posDef_diagonal_iff] at hc
  obtain ⟨⟨i, hi⟩, _⟩ := S.spectralRadius_isGreatest S.spectralBasis
  rw [← hi]
  change S.positiveBasis.eigenvalues i<Λ
  exact sub_pos.mp (hc i)

/-- Full exact source top-solution criterion for every actual finite
string with at least one physical gap. -/
theorem spectralRadius_lt_iff_top {Λ : ℝ} (hN : 0<N) :
    S.spectralRadius<Λ ↔
      (∀ k≤N,0<S.topA Λ k) ∧ (∀ k<N,0<S.topB Λ k) ∧ 0<S.topTerminal Λ := by
  constructor
  · intro hΛ
    exact ⟨S.topA_pos hΛ, S.topB_pos hΛ, S.topTerminal_pos hΛ hN⟩
  · rintro ⟨ha, _, ht⟩
    exact S.spectralRadius_lt_of_top hN ha ht

end
end krylov.Strings.DiscreteString

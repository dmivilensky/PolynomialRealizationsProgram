import krylov.Strings.DiscreteDivergence
import krylov.Strings.DiscretePolynomial
import krylov.Strings.DiscreteSpectral

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a)`, the genuine eigen-equation.
The literal physical polynomial recurrences solve every nonterminal row of
the independently constructed positive path operator. Irreducible forward
substitution then identifies them with the actual complete eigenvectors.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- The polynomial edge flux is exactly the source slope polynomial. -/
theorem polynomial_flux (ζ : ℝ) (k : ℕ) (hk : k < N) :
    (S.gap k)⁻¹ * ((S.φPolynomial k).eval ζ - (S.φPolynomial (k + 1)).eval ζ) =
      -(S.pPolynomial k).eval ζ := by
  rw [φPolynomial_succ, eval_add, eval_mul, eval_C]
  field_simp [(S.gap_pos k hk).ne']
  ring

/-- Actual slope increments include the distinguished initial unit atom. -/
theorem polynomial_mass_increment (ζ : ℝ) (k : ℕ) :
    (S.pPolynomial k).eval ζ -
      (if 0 < k then (S.pPolynomial (k - 1)).eval ζ else 0) =
        -ζ * S.mass k * (S.φPolynomial k).eval ζ := by
  cases k with
  | zero => simp [S.mass_zero]
  | succ k => simp only [pPolynomial_succ, eval_sub, eval_mul, eval_X, eval_C,
      Nat.zero_lt_succ, ite_true, Nat.add_sub_cancel]; ring

/-- The source position polynomials solve the actual physical matrix rows
before the terminal Robin boundary equation is imposed. -/
theorem polynomial_operator_row (ζ : ℝ) (i : Fin (N + 1)) (hi : i.val < N) :
    (S.operator *ᵥ S.massEmbedding (fun k ↦ (S.φPolynomial k).eval ζ)) i =
      ζ * S.massEmbedding (fun k ↦ (S.φPolynomial k).eval ζ) i := by
  rw [operator_massEmbedding_action, ite_eq_left hi,
    ite_eq_right (show i.val ≠ N by omega), add_zero, polynomial_flux S ζ i.val hi]
  have he := S.polynomial_mass_increment ζ i.val
  have hmass := Real.sq_sqrt (S.mass_pos i.val (by omega)).le
  have hsqrt : Real.sqrt (S.mass i.val) ≠ 0 :=
    (Real.sqrt_pos.mpr (S.mass_pos i.val (by omega))).ne'
  by_cases hp : 0 < i.val
  · have hpred : i.val - 1 + 1 = i.val := by omega
    have hflux := S.polynomial_flux ζ (i.val - 1) (by omega)
    rw [hpred] at hflux
    rw [ite_eq_left hp, hflux]
    rw [ite_eq_left hp] at he
    dsimp only [massEmbedding]
    field_simp
    rw [hmass]
    linear_combination -he
  · rw [ite_eq_right hp, sub_zero]
    rw [ite_eq_right hp, sub_zero] at he
    dsimp only [massEmbedding]
    field_simp
    rw [hmass]
    linear_combination -he

/-- Forward substitution needs only nonterminal physical rows. A zero first
coordinate forces the entire finite vector to vanish. -/
theorem first_rows_unique (ζ : ℝ) (x : Fin (N + 1) → ℝ)
    (hrows : ∀ i : Fin (N + 1), i.val < N → (S.operator *ᵥ x) i = ζ * x i)
    (hfirst : x 0 = 0) : x = 0 := by
  have hzero (n : ℕ) : ∀ i : Fin (N + 1), i.val ≤ n → x i = 0 := by
    induction n with
    | zero =>
      intro i hi
      have h : i = 0 := by
        apply Fin.ext
        change i.val = 0
        omega
      simpa only [h] using hfirst
    | succ n ih =>
      intro i hi
      by_cases hip : i.val ≤ n
      · exact ih i hip
      have hin : i.val = n + 1 := by omega
      let r : Fin (N + 1) := ⟨n, by omega⟩
      have hrN : r.val < N := by dsimp only [r]; omega
      have hs : (S.operator *ᵥ x) r = S.operator r i * x i := by
        change (∑ j : Fin (N + 1), S.operator r j * x j) = _
        apply Finset.sum_eq_single i
        · intro j _ hji
          by_cases hj : j.val ≤ n
          · rw [ih j hj, mul_zero]
          · rw [S.operator_tridiagonal r j (Or.inl (by
              have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
              dsimp only [r]
              omega)), zero_mul]
        · exact fun h ↦ (h (Finset.mem_univ i)).elim
      have he := hrows r hrN
      rw [hs, ih r (by dsimp only [r]; omega), mul_zero] at he
      exact (mul_eq_zero.mp he).resolve_left
        (S.operator_adjacent_neg r i (by dsimp only [r]; omega)).ne
  ext i
  exact hzero N i (by omega)

/-- Every column of the constructed physical eigenbasis satisfies the
actual operator eigen-equation. -/
theorem spectralBasis_column (k : Fin (N + 1)) (i : Fin (N + 1)) :
    (S.operator *ᵥ (fun j ↦ S.spectralBasis.Q j k)) i =
      S.spectralBasis.eigenvalues k * S.spectralBasis.Q i k := by
  have hm : S.operator * S.spectralBasis.Q =
      S.spectralBasis.Q * diagonal S.spectralBasis.eigenvalues := by
    calc
      _ = (S.spectralBasis.Q * diagonal S.spectralBasis.eigenvalues * S.spectralBasis.Qᵀ) *
          S.spectralBasis.Q := congrArg (fun A ↦ A * S.spectralBasis.Q) S.spectralBasis.reconstruct.symm
      _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_assoc,
        S.spectralBasis.transpose_mul, Matrix.mul_one]
  have h := congrArg (fun A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ ↦ A i k) hm
  rw [Matrix.mul_diagonal] at h
  change (S.operator *ᵥ (fun j ↦ S.spectralBasis.Q j k)) i = _ at h
  exact h.trans (mul_comm _ _)

/-- The source position polynomial is the actual normalized physical
eigenvector at every spectral node. The normalization uses the genuine
first-site component, which has already been proved nonzero. -/
theorem spectralBasis_polynomial (i k : Fin (N + 1)) :
    S.spectralBasis.Q i k = Real.sqrt (S.mass i.val) *
      (S.φPolynomial i.val).eval (S.spectralBasis.eigenvalues k) * S.spectralBasis.Q 0 k := by
  let ζ := S.spectralBasis.eigenvalues k
  let v : Fin (N + 1) → ℝ := fun j ↦ S.spectralBasis.Q j k
  let w := S.massEmbedding (fun n ↦ (S.φPolynomial n).eval ζ)
  let x := v - S.spectralBasis.Q 0 k • w
  have hx : x = 0 := by
    apply S.first_rows_unique ζ x
    · intro r hr
      simp only [x, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [show (S.operator *ᵥ v) r = ζ * v r from S.spectralBasis_column k r,
        show (S.operator *ᵥ w) r = ζ * w r from S.polynomial_operator_row ζ r hr]
      ring
    · simp [x, v, w, massEmbedding, S.mass_zero, ζ]
  have h := congrArg (fun y : Fin (N + 1) → ℝ ↦ y i) hx
  change S.spectralBasis.Q i k - S.spectralBasis.Q 0 k *
    (Real.sqrt (S.mass i.val) * (S.φPolynomial i.val).eval ζ) = 0 at h
  dsimp only [ζ] at h
  linear_combination h

end
end krylov.Strings.DiscreteString

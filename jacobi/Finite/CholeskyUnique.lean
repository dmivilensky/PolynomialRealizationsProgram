import jacobi.Finite.Gram

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The positive lower triangular Gram factor is unique. Thus the explicit factor
constructed by Gram--Schmidt agrees with any factor L satisfying the article's
hypotheses, so the polynomial transformation is independent of that choice.
Source: uniqueness of finite Cholesky factorization.
Use: turns the constructed Gram factor into the arbitrary L of the article's lemma.
-/
namespace jacobi.Finite.Gram
noncomputable section
open Matrix
open scoped BigOperators

/-- A positive lower triangular square root of a real Gram matrix is unique.
Use: turns the constructed Gram factor into the arbitrary L of the article's lemma.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: induct over rows and then columns. Earlier entries are already fixed;
an off-diagonal Gram entry determines the next entry by the positive pivot,
and the diagonal Gram entry determines the positive diagonal square root. -/
theorem positive_lower_unique {N : ℕ} (L K : Matrix (Fin N) (Fin N) ℝ)
    (hL : L.IsLowerTriangular) (hK : K.IsLowerTriangular)
    (hpL : ∀ i, 0 < L i i) (hpK : ∀ i, 0 < K i i)
    (hG : L * Lᵀ = K * Kᵀ) : L = K := by
  -- Earlier rows and earlier columns are already known; each Gram entry determines the next positive pivot.
  apply funext
  intro i
  induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin N → Fin N → Prop)).induction with
  | h i ih =>
    apply funext
    intro j
    induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin N → Fin N → Prop)).induction with
    | h j jh =>
      by_cases hij : i < j
      · rw [hL hij, hK hij]
      have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ => A i j) hG
      have hs : (∑ k, (L i k*L j k-K i k*K j k)) = 0 := by
        rw [Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr he
      have hz (k : Fin N) (hkj : k ≠ j) : L i k*L j k-K i k*K j k = 0 := by
        rcases lt_or_gt_of_ne hkj with hk | hk
        · rw [jh k hk]
          by_cases hji : j < i
          · rw [congrFun (ih j hji) k, sub_self]
          · have hji : j = i := le_antisymm (le_of_not_gt hij) (le_of_not_gt hji)
            subst j
            rw [jh k hk, sub_self]
        · rw [hL hk, hK hk, mul_zero, mul_zero, sub_self]
      rw [Finset.sum_eq_single j (fun k _ hk => hz k hk) (by simp)] at hs
      by_cases hji : j < i
      · rw [congrFun (ih j hji) j] at hs
        exact mul_right_cancel₀ (hpK j).ne' (sub_eq_zero.mp hs)
      · have hji : j = i := le_antisymm (le_of_not_gt hij) (le_of_not_gt hji)
        subst j
        nlinarith [hpL i, hpK i]

/-- Any positive lower triangular Gram factor equals the constructive one.
Use: the article's arbitrary Cholesky factor can be used in every inverse-coordinate formula.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: apply positive-factor uniqueness to the actual Gram--Schmidt factorization. -/
theorem factor_eq {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h : Module.finrank ℝ E = Fintype.card (Fin N))
    {f : Fin N → E} (hf : LinearIndependent ℝ f) (L : Matrix (Fin N) (Fin N) ℝ)
    (hL : L.IsLowerTriangular) (hp : ∀ i, 0 < L i i) (hG : Matrix.gram ℝ f = L*Lᵀ) :
    L = lower h f :=
  positive_lower_unique L _ hL (lower_triangular h f) hp (lower_invertible h hf).2
    (hG.symm.trans (factorization h f))

end
end jacobi.Finite.Gram

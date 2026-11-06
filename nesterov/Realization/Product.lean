import polyak.Realization.Product

/-!
Article: Lemma `lem:startup`, arbitrary initial query repair.
Use: only pairs away from the changed initial datum must already interpolate.
The initial position, gradient and value can all be replaced. This is the
extension of Polyak's scalar reserve argument required by extrapolated queries.
-/
namespace nesterov.Realization
noncomputable section
open polyak polyak.Interpolation polyak.Realization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: all untouched pairs stay feasible after the positive scalar reserve is added. -/
theorem untouched_pair_bound {x σ : Option ℕ → E} {v : Option ℕ → ℝ}
    (h : ∀ i j,i≠some 0 → j≠some 0 → |datumT x σ v i j|≤datumR x σ i j) (b : E) (y : Option ℕ → ℝ) {τ : ℝ} (hτ : |τ|<1)
    {i j : Option ℕ} (hi : i≠some 0) (hj : j≠some 0) :
    |datumT (productPosition x y) (productGradient (correctGradient σ b) y τ)
      (productValue (correctValue x v b) y τ) i j|  ≤ 
      datumR (productPosition x y) (productGradient (correctGradient σ b) y τ) i j := by
  rw [datumT_product,datumR_product]
  simp only [datumT,datumR,correctGradient,correctValue,hi,hj,↓reduceIte] at *
  have hc : 0 ≤ 1-τ^2 := by have := abs_lt.mp hτ; nlinarith [sq_abs τ]
  exact (h i j hi hj).trans (le_add_of_nonneg_right (by positivity))

/-- Article: startup interpolation. Use: one scalar coordinate repairs every exceptional pair,
including the minimizer and every positive index in the infinite table. -/
theorem repaired_tableFeasible_off_initial {x σ : Option ℕ → E} {v : Option ℕ → ℝ}
    (h : ∀ i j,i≠some 0 → j≠some 0 → |datumT x σ v i j|≤datumR x σ i j) (hx : x none=0) (hσ : σ none=0) (hv : v none=0)
    (b : E) (p : ℕ → ℝ) (hp₀ : p 0=1) {τ M Y : ℝ} (hτ : |τ|<1)
    (hM : ∀ k,1 ≤ k → ∀ δ,δ=1 ∨ δ= -1 →
      -M ≤ initialPairSlack (x (some 0)) b (x (some k)) (σ (some k)) (v (some k)) δ)
    (hYstar : ‖b‖^2/4 ≤ (1/4 : ℝ)*(1-τ^2)*Y^2)
    (hYpair : ∀ k,1 ≤ k → M ≤ (1/4 : ℝ)*(1-τ^2)*Y^2*(1-p k)^2) :
    TableFeasible (productPosition x (scalarPosition p Y))
      (productGradient (correctGradient σ b) (scalarPosition p Y) τ)
      (productValue (correctValue x v b) (scalarPosition p Y) τ) := by
  let X := productPosition x (scalarPosition p Y)
  let S := productGradient (correctGradient σ b) (scalarPosition p Y) τ
  let V := productValue (correctValue x v b) (scalarPosition p Y) τ
  have hstar : |datumT X S V none (some 0)| ≤ datumR X S none (some 0) := by
    change |datumT (productPosition _ _) (productGradient _ _ _) (productValue _ _ _) _ _| ≤ 
      datumR (productPosition _ _) (productGradient _ _ _) _ _
    rw [datumT_product,datumR_product]
    simp only [datumT,datumR,correctGradient,correctValue,scalarPosition,hx,hσ,hv,hp₀,
      zero_add,sub_zero,mul_one,reduceCtorEq,↓reduceIte,sub_self,abs_zero]
    nlinarith [sq_nonneg ‖x (some 0)‖]
  have hpair (k : ℕ) (hk : 1 ≤ k) : |datumT X S V (some 0) (some k)| ≤ datumR X S (some 0) (some k) := by
    have he (δ : ℝ) : datumR X S (some 0) (some k)+δ*datumT X S V (some 0) (some k)=
        initialPairSlack (x (some 0)) b (x (some k)) (σ (some k)) (v (some k)) δ+
          (1/4 : ℝ)*(1-τ^2)*Y^2*(1-p k)^2 := by
      change datumR (productPosition _ _) (productGradient _ _ _) _ _+δ*
        datumT (productPosition _ _) (productGradient _ _ _) (productValue _ _ _) _ _ = _
      rw [datumT_product,datumR_product]
      have hn : (some k : Option ℕ)≠some 0 := by simp; omega
      simp only [datumT,datumR,correctGradient,correctValue,scalarPosition,hp₀,
        hn,↓reduceIte,mul_one,initialPairSlack,Energy.pairQuadratic]
      ring
    have hlo := hM k hk 1 (Or.inl rfl)
    have hup := hM k hk (-1) (Or.inr rfl)
    have hys := hYpair k hk
    have hl := he 1
    have hu := he (-1)
    simp only [one_mul,neg_one_mul] at hl hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro i j
  change |datumT X S V i j| ≤ datumR X S i j
  by_cases hi : i=some 0
  · subst i
    cases j with
    | none =>
      rw [datumT_antisymm,abs_neg,datumR_symm]
      exact hstar
    | some k =>
      by_cases hk : k=0
      · subst k; simp [datumT,datumR]
      · exact hpair k (by omega)
  · by_cases hj : j=some 0
    · subst j
      cases i with
      | none => exact hstar
      | some k =>
        rw [datumT_antisymm,abs_neg,datumR_symm]
        exact hpair k (by simp only [Option.some.injEq] at hi; omega)
    · exact untouched_pair_bound h b (scalarPosition p Y) hτ hi hj


/-- A bounded wave family may have any finite amplitude, not just unit norm. -/
theorem exists_initial_deficit_bound (a b : E) (x σ : ℕ→E) (v : ℕ→ℝ)
    (hσ : ∀ k,‖σ k‖≤‖x k‖)
    (hstar : ∀ k δ,δ=1 ∨ δ= -1 → 0≤originSlack (x k) (σ k) (v k) δ)
    (hcontrol : (∃ B : ℝ,∀ k,‖x k‖≤B) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖x k‖^2≤originSlack (x k) (σ k) (v k) δ) :
    ∃ M : ℝ,0≤M ∧ ∀ k δ,δ=1 ∨ δ= -1 →
      -M ≤ initialPairSlack a b (x k) (σ k) (v k) δ := by
  rcases hcontrol with ⟨B,hB⟩ | hstrict
  · have hBp : 0≤B := (norm_nonneg (x 0)).trans (hB 0)
    refine ⟨(‖a‖+‖b‖)*B+‖b‖^2/4,by positivity,fun k δ hδ => ?_⟩
    have hh := initialPairSlack_ge a b (x k) (σ k) (v k) δ hδ (hσ k)
    have hm := mul_le_mul_of_nonneg_left (hB k) (add_nonneg (norm_nonneg a) (norm_nonneg b))
    linarith [hstar k δ hδ]
  · exact exists_initialPairSlack_lower_bound a b x σ v hσ hstar (Or.inr hstrict)

/-- The normalized scalar curvature of every interior original quadratic is strict. -/
theorem normalized_scalar_abs_lt_one {μ L lam : ℝ} (hμL : μ<L) (hlam : lam∈Set.Ioo μ L) :
    |(L+μ-2*lam)/(L-μ)|<1 := by
  rw [abs_lt]
  constructor
  · exact (lt_div_iff₀ (sub_pos.mpr hμL)).mpr (by linarith [hlam.2])
  · exact (div_lt_iff₀ (sub_pos.mpr hμL)).mpr (by linarith [hlam.1])

end
end nesterov.Realization

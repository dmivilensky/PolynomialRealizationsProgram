import polyak.Realization.Auxiliary
import polyak.Realization.Bounds
import polyak.Interpolation.Extension
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Article: Appendix A, the orthogonal scalar startup coordinate.
Use: repair the complete infinite interpolation table using one finite amplitude.
Proof: T adds with zero scalar contribution and R adds a positive squared-distance reserve.
-/

namespace polyak.Realization
noncomputable section
open Interpolation

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: the orthogonal sum of mode positions and the added real coordinate. -/
def productPosition (x : I → E) (y : I → ℝ) (i : I) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (x i,y i)

/-- Article: the scalar coordinate carries the quadratic gradient τy. -/
def productGradient (σ : I → E) (y : I → ℝ) (τ : ℝ) (i : I) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (σ i,τ*y i)

/-- Article: add the actual scalar quadratic value. -/
def productValue (v y : I → ℝ) (τ : ℝ) (i : I) : ℝ := v i+τ/2*y i^2

/-- Article: scalar quadratic adds no signed discrepancy. -/
theorem datumT_product (x σ : I → E) (v y : I → ℝ) (τ : ℝ) (i j : I) :
    datumT (productPosition x y) (productGradient σ y τ) (productValue v y τ) i j =
      datumT x σ v i j := by
  simp only [datumT,productPosition,productGradient,productValue,WithLp.prod_inner_apply,
    WithLp.ofLp_add,WithLp.ofLp_sub,Real.inner_apply,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub]
  change v j+τ/2*y j^2-(v i+τ/2*y i^2)-
    (1/2 : ℝ)*(inner ℝ (σ i+σ j) (x j-x i)+(τ*y i+τ*y j)*(y j-y i)) = _
  ring

omit [InnerProductSpace ℝ E] in
/-- Article: positive interpolation reserve in the scalar coordinate. -/
theorem datumR_product (x σ : I → E) (y : I → ℝ) (τ : ℝ) (i j : I) :
    datumR (productPosition x y) (productGradient σ y τ) i j =
      datumR x σ i j+(1/4 : ℝ)*(1-τ^2)*(y j-y i)^2 := by
  simp only [datumR,productPosition,productGradient,WithLp.prod_norm_sq_eq_of_L2]
  change (1/4 : ℝ)*((‖x j-x i‖^2+‖y j-y i‖^2)-
    (‖σ j-σ i‖^2+‖τ*y j-τ*y i‖^2)) = _
  simp only [Real.norm_eq_abs,sq_abs]
  ring

/-- Article: corrected initial gradient. Use: all positive-time mode gradients remain unchanged. -/
def correctGradient (σ : Option ℕ → E) (b : E) (i : Option ℕ) : E :=
  if i=some 0 then b else σ i

/-- Article: corrected initial value. Use: T⋆₀=0 exactly. -/
def correctValue (x : Option ℕ → E) (v : Option ℕ → ℝ) (b : E) (i : Option ℕ) : ℝ :=
  if i=some 0 then (1/2 : ℝ)*inner ℝ b (x (some 0)) else v i

/-- Article: added scalar positions, including the zero minimizer datum. -/
def scalarPosition (p : ℕ → ℝ) (Y : ℝ) : Option ℕ → ℝ
  | none => 0
  | some k => Y*p k

omit [InnerProductSpace ℝ E] in
/-- Article: choose one amplitude for all interpolation repairs. -/
theorem exists_reserve_amplitude {τ M : ℝ} (hτ : |τ|<1) (hM : 0 ≤ M)
    (p : ℕ → ℝ) (hgap : ∃ δ : ℝ,0<δ ∧ ∀ k,1 ≤ k → δ ≤ (1-p k)^2) (b : E) :
    ∃ Y : ℝ, 0<Y ∧ ‖b‖^2/4 ≤ (1/4 : ℝ)*(1-τ^2)*Y^2 ∧
      ∀ k,1 ≤ k → M ≤ (1/4 : ℝ)*(1-τ^2)*Y^2*(1-p k)^2 := by
  obtain ⟨δ,hδ,hg⟩ := hgap
  let c : ℝ := (1/4 : ℝ)*(1-τ^2)
  have hc : 0<c := by
    have hh := abs_lt.mp hτ
    dsimp [c]
    nlinarith [sq_abs τ]
  let d := min δ 1
  have hd : 0<d := lt_min hδ zero_lt_one
  let Y := Real.sqrt ((M+‖b‖^2+1)/(c*d))
  have hY : 0<Y := Real.sqrt_pos.mpr (div_pos (by positivity) (mul_pos hc hd))
  have hsq : Y^2=(M+‖b‖^2+1)/(c*d) := Real.sq_sqrt (by positivity)
  have he : c*Y^2*d=M+‖b‖^2+1 := by rw [hsq]; field_simp
  have hbase : c*Y^2*d ≤ c*Y^2 := mul_le_of_le_one_right (by positivity) (min_le_right _ _)
  refine ⟨Y,hY,by change _ ≤ c*Y^2; nlinarith [sq_nonneg ‖b‖],fun k hk => ?_⟩
  have hdk : d ≤ (1-p k)^2 := (min_le_left _ _).trans (hg k hk)
  have hh := mul_le_mul_of_nonneg_left hdk (show 0 ≤ c*Y^2 by positivity)
  change M ≤ c*Y^2*(1-p k)^2
  nlinarith [sq_nonneg ‖b‖]

/-- Article: all untouched pairs stay feasible after the positive scalar reserve is added. -/
theorem unchanged_pair_bound {x σ : Option ℕ → E} {v : Option ℕ → ℝ}
    (h : TableFeasible x σ v) (b : E) (y : Option ℕ → ℝ) {τ : ℝ} (hτ : |τ|<1)
    {i j : Option ℕ} (hi : i≠some 0) (hj : j≠some 0) :
    |datumT (productPosition x y) (productGradient (correctGradient σ b) y τ)
      (productValue (correctValue x v b) y τ) i j|  ≤ 
      datumR (productPosition x y) (productGradient (correctGradient σ b) y τ) i j := by
  rw [datumT_product,datumR_product]
  simp only [datumT,datumR,correctGradient,correctValue,hi,hj,↓reduceIte] at *
  have hc : 0 ≤ 1-τ^2 := by have := abs_lt.mp hτ; nlinarith [sq_abs τ]
  exact (h i j).trans (le_add_of_nonneg_right (by positivity))

/-- Article: startup interpolation. Use: one scalar coordinate repairs every exceptional pair,
including the minimizer and every positive index in the infinite table. -/
theorem repaired_tableFeasible {x σ : Option ℕ → E} {v : Option ℕ → ℝ}
    (h : TableFeasible x σ v) (hx : x none=0) (hσ : σ none=0) (hv : v none=0)
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
    · exact unchanged_pair_bound h b (scalarPosition p Y) hτ hi hj

end
end polyak.Realization

import nesterov.Realization.Product

/-!
Article: Lemma `lem:startup`, one potential for the complete infinite table.
Use: the initial wave query may be replaced by the physical from-rest point;
one auxiliary coordinate repairs every changed pair simultaneously.
-/
namespace nesterov.Realization
noncomputable section
open polyak polyak.Interpolation polyak.Realization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def correctPosition (x : Option ℕ→E) (a : E) (i : Option ℕ) : E :=
  if i=some 0 then a else x i

theorem exists_startup_potential {τ : ℝ} (hτ : |τ|<1)
    (p : ℕ→ℝ) (hp0 : p 0=1)
    (hgap : ∃ η : ℝ,0<η ∧ ∀ k : ℕ,1≤k → η≤(1-p k)^2)
    (x σ : Option ℕ→E) (v : Option ℕ→ℝ)
    (h : TableFeasible x σ v) (hx : x none=0) (hσ : σ none=0) (hv : v none=0)
    (hcontrol : (∃ B : ℝ,∀ k,‖x (some k)‖≤B) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖x (some k)‖^2≤originSlack (x (some k)) (σ (some k)) (v (some k)) δ)
    (a b : E) :
    ∃ Y : ℝ,∃ ψ : WithLp 2 (E×ℝ)→ℝ,0<Y ∧ NormalizedSmooth ψ ∧
      ∀ i,ψ (productPosition (correctPosition x a) (scalarPosition p Y) i)=
        productValue (correctValue (correctPosition x a) v b) (scalarPosition p Y) τ i ∧
      gradient ψ (productPosition (correctPosition x a) (scalarPosition p Y) i)=
        productGradient (correctGradient σ b) (scalarPosition p Y) τ i := by
  have hsg (k : ℕ) : ‖σ (some k)‖≤‖x (some k)‖ := by
    have hh := (abs_nonneg _).trans (h none (some k))
    simp only [datumR,hx,hσ,sub_zero] at hh
    nlinarith [norm_nonneg (σ (some k)),norm_nonneg (x (some k))]
  have hstar (k : ℕ) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) :
      0≤originSlack (x (some k)) (σ (some k)) (v (some k)) δ := by
    have hh := abs_le.mp (h none (some k))
    simp only [datumR,datumT,hx,hσ,hv,sub_zero,zero_add] at hh
    rcases hδ with rfl | rfl <;> unfold originSlack <;> linarith [hh.1,hh.2]
  obtain ⟨M,hM,hdef⟩ := exists_initial_deficit_bound a b
    (fun k=>x (some k)) (fun k=>σ (some k)) (fun k=>v (some k)) hsg hstar hcontrol
  obtain ⟨Y,hY,hYs,hYp⟩ := exists_reserve_amplitude hτ hM p hgap b
  have hoff : ∀ i j,i≠some 0 → j≠some 0 →
      |datumT (correctPosition x a) σ v i j|≤datumR (correctPosition x a) σ i j := by
    intro i j hi hj
    simpa only [datumT,datumR,correctPosition,ite_eq_right hi,ite_eq_right hj] using h i j
  have hx' : correctPosition x a none=0 := by simp [correctPosition,hx]
  have hdef' (k : ℕ) (hk : 1≤k) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) :
      -M ≤ initialPairSlack (correctPosition x a (some 0)) b
        (correctPosition x a (some k)) (σ (some k)) (v (some k)) δ := by
    have hk' : (some k : Option ℕ)≠some 0 := by simp; omega
    simpa [correctPosition,hk'] using hdef k δ hδ
  have htable := repaired_tableFeasible_off_initial hoff hx' hσ hv b p hp0 hτ hdef' hYs hYp
  have hX : productPosition (correctPosition x a) (scalarPosition p Y) none=0 := by
    simp [productPosition,scalarPosition,hx']
  have hS : productGradient (correctGradient σ b) (scalarPosition p Y) τ none=0 := by
    simp [productGradient,correctGradient,scalarPosition,hσ]
  have hV : productValue (correctValue (correctPosition x a) v b) (scalarPosition p Y) τ none=0 := by
    simp [productValue,correctValue,scalarPosition,hv]
  obtain ⟨ψ,hψ,hdata⟩ := exists_normalized_interpolant htable none hX hS hV
  exact ⟨Y,ψ,hY,hψ,hdata⟩

end
end nesterov.Realization

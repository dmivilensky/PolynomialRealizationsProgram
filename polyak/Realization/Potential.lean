import polyak.Realization.Product

/-!
Article: Appendix A, Lemma startup, one global interpolating potential.
Use: the added coordinate fixes all exceptional pairs at once, for unbounded infinite data.
Proof: select the stable nonreturning response, choose one amplitude, and apply arbitrary-set interpolation.
-/

namespace polyak.Realization
noncomputable section
open Interpolation Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: initialized positions including the minimizer. -/
def startupPosition (x : Option ℕ → E) (A B β τ Y : ℝ) : Option ℕ → WithLp 2 (E × ℝ) :=
  productPosition x (scalarPosition (response (A+B*τ) β) Y)

/-- Article: initialized gradients with exactly one corrected mode datum. -/
def startupGradient (σ : Option ℕ → E) (b : E) (A B β τ Y : ℝ) : Option ℕ → WithLp 2 (E × ℝ) :=
  productGradient (correctGradient σ b) (scalarPosition (response (A+B*τ) β) Y) τ

/-- Article: initialized values including the quadratic coordinate. -/
def startupValue (x : Option ℕ → E) (v : Option ℕ → ℝ) (b : E)
    (A B β τ Y : ℝ) : Option ℕ → ℝ :=
  productValue (correctValue x v b) (scalarPosition (response (A+B*τ) β) Y) τ

/-- Article: stability of the chosen coordinate. Use: strict normalized stability survives every |τ|<1. -/
theorem scalar_stable {A B β τ : ℝ} (hB : 0<B) (hA : |A|+B<1+β) (hτ : |τ|<1) :
    |A+B*τ|<1+β := by
  calc
    |A+B*τ| ≤ |A|+|B*τ| := abs_add_le _ _
    _ = |A|+B*|τ| := by rw [abs_mul,abs_of_pos hB]
    _ < |A|+B := by nlinarith
    _ < _ := hA

/-- Article: startup with a fixed auxiliary coefficient. Use: in particular Polyak's explicit τ=0.
Proof: the same complete repair argument requires only decay and absence of positive-time returns. -/
theorem exists_startup_potential_fixed {A B β τ : ℝ} (hτ : |τ|<1)
    (hno : ∀ k,1 ≤ k → response (A+B*τ) β k≠1)
    (hlim : Tendsto (response (A+B*τ) β) atTop (𝓝 0))
    (x σ : Option ℕ → E) (v : Option ℕ → ℝ)
    (h : TableFeasible x σ v) (hx : x none=0) (hσ : σ none=0) (hv : v none=0)
    (hcontrol : (∀ k, ‖x (some k)‖ ≤ 1) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖x (some k)‖^2 ≤ originSlack (x (some k)) (σ (some k)) (v (some k)) δ)
    (b : E) :
    ∃ Y : ℝ, ∃ ψ : WithLp 2 (E × ℝ) → ℝ,
      0<Y ∧ NormalizedSmooth ψ ∧
      ∀ i, ψ (startupPosition x A B β τ Y i)=startupValue x v b A B β τ Y i ∧
        gradient ψ (startupPosition x A B β τ Y i)=startupGradient σ b A B β τ Y i := by
  obtain ⟨δ,hδ,hgap⟩ := uniform_return_gap (response (A+B*τ) β) hno hlim
  have hsg (k : ℕ) : ‖σ (some k)‖ ≤ ‖x (some k)‖ := by
    have hh := (abs_nonneg _).trans (h none (some k))
    simp only [datumR,hx,hσ,sub_zero] at hh
    nlinarith [norm_nonneg (σ (some k)),norm_nonneg (x (some k))]
  have hstar (k : ℕ) (δ : ℝ) (hδ : δ=1 ∨ δ= -1) :
      0 ≤ originSlack (x (some k)) (σ (some k)) (v (some k)) δ := by
    have hh := abs_le.mp (h none (some k))
    simp only [datumR,datumT,hx,hσ,hv,sub_zero,zero_add] at hh
    rcases hδ with rfl | rfl <;> unfold originSlack <;> linarith [hh.1,hh.2]
  obtain ⟨M,hM,hdef⟩ := exists_initialPairSlack_lower_bound (x (some 0)) b
    (fun k => x (some k)) (fun k => σ (some k)) (fun k => v (some k)) hsg hstar hcontrol
  obtain ⟨Y,hY,hYs,hYp⟩ := exists_reserve_amplitude hτ hM (response (A+B*τ) β) ⟨δ,hδ,hgap⟩ b
  have htable := repaired_tableFeasible h hx hσ hv b (response (A+B*τ) β)
    (response_zero _ _) hτ (fun k _ δ hδ => hdef k δ hδ) hYs hYp
  have hX : startupPosition x A B β τ Y none=0 := by simp [startupPosition,productPosition,scalarPosition,hx]
  have hS : startupGradient σ b A B β τ Y none=0 := by
    simp [startupGradient,productGradient,correctGradient,scalarPosition,hσ]
  have hV : startupValue x v b A B β τ Y none=0 := by
    simp [startupValue,productValue,correctValue,scalarPosition,hv]
  obtain ⟨ψ,hψ,hdata⟩ := exists_normalized_interpolant htable none hX hS hV
  exact ⟨Y,ψ,hY,hψ,hdata⟩


/-- Article: one-coordinate startup, full infinite interpolation.
Use: a single potential and a single amplitude serve every horizon.
The alternative hypotheses are bounded modes or a strict minimizer reserve. -/
theorem exists_startup_potential {A B β : ℝ} (hB : 0<B) (hβ : 0 ≤ β) (hβ1 : β<1)
    (hA : |A|+B<1+β) (x σ : Option ℕ → E) (v : Option ℕ → ℝ)
    (h : TableFeasible x σ v) (hx : x none=0) (hσ : σ none=0) (hv : v none=0)
    (hcontrol : (∀ k, ‖x (some k)‖ ≤ 1) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖x (some k)‖^2 ≤ originSlack (x (some k)) (σ (some k)) (v (some k)) δ)
    (b : E) :
    ∃ τ Y : ℝ, ∃ ψ : WithLp 2 (E × ℝ) → ℝ,
      |τ|<1 ∧ 0<Y ∧ NormalizedSmooth ψ ∧
      Tendsto (response (A+B*τ) β) atTop (𝓝 0) ∧
      ∀ i, ψ (startupPosition x A B β τ Y i)=startupValue x v b A B β τ Y i ∧
        gradient ψ (startupPosition x A B β τ Y i)=startupGradient σ b A B β τ Y i := by
  obtain ⟨τ,hτ,hno⟩ := exists_scalar_coefficient (A := A) (β := β) hB
  have hlim := response_tendsto_zero hβ hβ1 (scalar_stable hB hA hτ)
  obtain ⟨Y,ψ,hY,hψ,hdata⟩ := exists_startup_potential_fixed hτ hno hlim
    x σ v h hx hσ hv hcontrol b
  exact ⟨τ,Y,ψ,hτ,hY,hψ,hlim,hdata⟩

end
end polyak.Realization

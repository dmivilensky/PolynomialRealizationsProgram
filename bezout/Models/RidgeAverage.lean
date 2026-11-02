import bezout.Models.RidgeDesign

/-!
Article: bezout, the average worker objective in Equation `eq:experiment-ridge`.
Use: the displayed condition on the average linear worker term makes x-star
a genuine global minimizer of the actual average ridge objective.
Proof: average the exact quadratic differences; all linear terms cancel.
-/

namespace bezout.Models.Ridge
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {W : Type*} [Fintype W] [Nonempty W]

/-- The actual mean of all worker ridge objectives. -/
def averageObjective (d ρ : ℝ) (A : E →L[ℝ] E) (z : W → E) (x : E) : ℝ :=
  (1/(Fintype.card W:ℝ))*∑ i, objective d ρ A (z i) x

/-- Averaging a compatible collection of literal worker objectives has x-star as minimizer. -/
theorem average_minimizer (d ρ : ℝ) (hd : 0<d) (A H : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (z c : W → E) (xstar : E)
    (hAA : ∀ v, A (A v)=d • (H v-ρ • v)) (hAz : ∀ i, A (z i)=d • c i)
    (hmean : (1/(Fintype.card W:ℝ)) • (∑ i, c i)=H xstar)
    (hH : ∀ y, 0 ≤ inner ℝ (H y) y) :
    ∀ x, averageObjective d ρ A z xstar≤averageObjective d ρ A z x := by
  have hm0 : (Fintype.card W:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ i, c i)=(Fintype.card W:ℝ) • H xstar := by
    have h := congrArg (fun u : E => (Fintype.card W:ℝ) • u) hmean
    simpa only [smul_smul, mul_one_div_cancel hm0, one_smul] using h
  intro x
  let y := x-xstar
  have hc : (∑ i, inner ℝ (H xstar-c i) y)=0 := by
    rw [← sum_inner, Finset.sum_sub_distrib, Finset.sum_const, hsum]
    simp only [Finset.card_univ, Nat.cast_smul_eq_nsmul, sub_self, inner_zero_left]
  have hf : averageObjective d ρ A z x-averageObjective d ρ A z xstar=
      (1/2)*inner ℝ (H y) y := by
    have hp (i : W) := objective_difference d ρ hd A H hA (z i) (c i) xstar y hAA (hAz i)
    have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset W)) rfl (fun i _ => hp i)
    simp only [y, add_sub_cancel] at hs
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hc, zero_add, Finset.sum_const] at hs
    unfold averageObjective
    rw [← mul_sub, hs, nsmul_eq_mul]
    field_simp
    simp only [Finset.card_univ, y]
  have hp := hH y
  linarith

/-- The fully constructed distributed rank-one ridge problem has the prescribed minimizer. -/
theorem design_average_minimizer (d : ℝ) (hd : 0<d) (v : E) (hv : ‖v‖=1)
    (μ L ρ : ℝ) (hμ : 0≤μ) (hμL : μ≤L) (hρ : ρ<μ) (c : W → E) (xstar : E)
    (hmean : (1/(Fintype.card W:ℝ)) • (∑ i, c i)=spectralMap v μ L xstar) :
    ∀ x, averageObjective d ρ (design d v μ L ρ) (fun i => label d v μ L ρ (c i)) xstar≤
      averageObjective d ρ (design d v μ L ρ) (fun i => label d v μ L ρ (c i)) x := by
  have hρL : ρ<L := hρ.trans_le hμL
  apply average_minimizer d ρ hd _ _ (design_symmetric d v μ L ρ) _ c xstar
    (design_identities d hd.le v hv μ L ρ hρ hρL 0).1
    (fun i => (design_identities d hd.le v hv μ L ρ hρ hρL (c i)).2) hmean
  exact spectralMap_nonneg v μ L hμ hμL

end
end bezout.Models.Ridge

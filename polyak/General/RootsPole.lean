import polyak.General.RootsDominant

/-! Article: Theorem B(b), the actual simple negative pole at the dominant b-root. -/
namespace polyak.General
noncomputable section
namespace Tuning

def poleResidue (q : Tuning) : ℝ :=
  (1+q.rhoB)*(q.y-q.x)*q.rhoB/(-q.rhoB+q.beta/q.rhoB)
def poleQuotient (q : Tuning) (z : ℂ) : ℂ :=
  -(z^2+z*(-q.rhoB : ℂ)+(-q.rhoB : ℂ)^2)+
    (1+(1+q.beta-q.x : ℝ))*(z+(-q.rhoB : ℂ))-(1+q.beta-q.x+q.beta : ℝ)

theorem poleResidue_neg (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) : q.poleResidue<0 := by
  obtain ⟨hr,_,hi,_⟩ := q.dominant_b_root h hab
  rw [neg_div] at hi
  apply div_neg_of_pos_of_neg
  · exact mul_pos (mul_pos (by linarith) (sub_pos.2 q.x_lt_y)) hr
  · linarith

theorem a_at_negative_pole (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) : q.a (-q.rhoB : ℂ)=((q.y-q.x)*q.rhoB : ℝ) := by
  obtain ⟨_,hb,_,_⟩ := q.dominant_b_root h hab
  have he := q.a_sub_b (-q.rhoB : ℂ)
  rw [hb,sub_zero] at he
  rw [he]
  push_cast
  ring

theorem negative_pole_decomposition (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) {z : ℂ} (hz : z+(q.rhoB : ℂ)≠0)
    (hz' : z+(q.beta/q.rhoB : ℝ)≠0) :
    (1-z)*q.a z/q.b z=(q.poleResidue : ℂ)/(z+(q.rhoB : ℂ))+
      (q.poleQuotient z-(q.poleResidue : ℂ))/(z+(q.beta/q.rhoB : ℝ)) := by
  obtain ⟨hr,_,hi,_⟩ := q.dominant_b_root h hab
  rw [neg_div] at hi
  have hdiff : -q.rhoB+q.beta/q.rhoB≠0 := by linarith
  have hdc : ((-q.rhoB+q.beta/q.rhoB : ℝ):ℂ)≠0 := by exact_mod_cast hdiff
  have ha := q.a_at_negative_pole h hab
  rw [q.dominant_b_factor h hab]
  have hκ : (q.poleResidue : ℂ)*((-q.rhoB+q.beta/q.rhoB : ℝ):ℂ)=
      (1+(q.rhoB : ℂ))*q.a (-q.rhoB : ℂ) := by
    rw [ha]
    rw [poleResidue,Complex.ofReal_div]
    rw [div_mul_cancel₀ _ hdc]
    push_cast
    ring
  have he (w : ℂ) : (1-w)*q.a w-
      (1+(q.rhoB : ℂ))*q.a (-q.rhoB : ℂ)=(w+(q.rhoB : ℂ))*q.poleQuotient w := by
    dsimp [a,poleQuotient]
    push_cast
    ring
  have he' := he z
  field_simp [hz,hz']
  push_cast at hκ ⊢
  linear_combination he' - hκ

end Tuning
end
end polyak.General

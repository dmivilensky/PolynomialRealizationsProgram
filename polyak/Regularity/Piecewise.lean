import Mathlib.Order.Monotone.Union
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: Theorem classification, monotonicity across the finitely many switches.
Use: strictly increasing closed arcs agree at their shared endpoints because
they are restrictions of the same actual function.
-/
namespace polyak.Regularity
open Set

theorem strictMonoOn_join_left {f : ℝ → ℝ} {a b : ℝ} (hab : a≤b)
    (hl : StrictMonoOn f (Iic a)) (hr : StrictMonoOn f (Icc a b)) :
    StrictMonoOn f (Iic b) := by
  intro x hx y hy hxy
  by_cases hya : y≤a
  · exact hl (hxy.le.trans hya) hya hxy
  by_cases hax : a≤x
  · exact hr ⟨hax,hx⟩ ⟨hax.trans hxy.le,hy⟩ hxy
  · exact (hl (lt_of_not_ge hax).le (mem_Iic.mpr le_rfl) (lt_of_not_ge hax)).trans
      (hr ⟨le_rfl,hab⟩ ⟨(lt_of_not_ge hya).le,hy⟩ (lt_of_not_ge hya))

theorem strictMono_of_seven_arcs {f : ℝ → ℝ} {a b c : ℝ}
    (ha : 0≤a) (hab : a≤b) (hbc : b≤c)
    (h₀ : StrictMonoOn f (Iic (-c)))
    (h₁ : StrictMonoOn f (Icc (-c) (-b)))
    (h₂ : StrictMonoOn f (Icc (-b) (-a)))
    (h₃ : StrictMonoOn f (Icc (-a) a))
    (h₄ : StrictMonoOn f (Icc a b))
    (h₅ : StrictMonoOn f (Icc b c))
    (h₆ : StrictMonoOn f (Ici c)) : StrictMono f := by
  have hm₁ := strictMonoOn_join_left (neg_le_neg hbc) h₀ h₁
  have hm₂ := strictMonoOn_join_left (neg_le_neg hab) hm₁ h₂
  have hm₃ := strictMonoOn_join_left (by linarith : -a≤a) hm₂ h₃
  have hm₄ := strictMonoOn_join_left hab hm₃ h₄
  exact (strictMonoOn_join_left hbc hm₄ h₅).Iic_union_Ici h₆

theorem strictMono_of_deriv_pos_away_abs_cuts {f : ℝ → ℝ} {a b c : ℝ}
    (ha : 0<a) (hab : a<b) (hbc : b<c) (hf : Continuous f)
    (hd : ∀ t : ℝ,|t|≠a → |t|≠b → |t|≠c → 0<deriv f t) : StrictMono f := by
  apply strictMono_of_seven_arcs ha.le hab.le hbc.le
  · apply strictMonoOn_of_deriv_pos (convex_Iic _) hf.continuousOn
    intro t ht
    rw [interior_Iic] at ht
    have htc : t< -c := ht
    have ht0 : t<0 := by linarith
    apply hd t <;> rw [abs_of_neg ht0] <;> linarith [show t< -c from ht]
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : t<0 := by linarith [ht.2]
    apply hd t <;> rw [abs_of_neg ht0] <;> linarith [ht.1,ht.2]
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : t<0 := by linarith [ht.2]
    apply hd t <;> rw [abs_of_neg ht0] <;> linarith [ht.1,ht.2]
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have htabs : |t|<a := abs_lt.mpr ht
    apply hd t <;> linarith
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0<t := by linarith [ht.1]
    apply hd t <;> rw [abs_of_pos ht0] <;> linarith [ht.1,ht.2]
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro t ht
    rw [interior_Icc] at ht
    have ht0 : 0<t := by linarith [ht.1]
    apply hd t <;> rw [abs_of_pos ht0] <;> linarith [ht.1,ht.2]
  · apply strictMonoOn_of_deriv_pos (convex_Ici _) hf.continuousOn
    intro t ht
    rw [interior_Ici] at ht
    have htc : c<t := ht
    have ht0 : 0<t := by linarith
    apply hd t <;> rw [abs_of_pos ht0] <;> linarith [show c<t from ht]

end polyak.Regularity

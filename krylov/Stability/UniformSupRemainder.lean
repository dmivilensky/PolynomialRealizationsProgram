import krylov.Stability.CompactSmooth
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, genuine supremum transfer of a uniform remainder.
Use: pass an actual common vector remainder and attained linear matrix maximum
to a two-sided bound on the true nonlinear worst-output supremum.
Source: the real norm triangle inequality and conditionally complete real
supremum bounds; neither a nonlinear maximizer nor a desired expansion is assumed.
-/

namespace krylov.Stability
noncomputable section
variable {Y F : Type*} [NormedAddCommGroup F]

/-- A common genuine vector remainder transfers an attained linear norm
maximum to the true nonlinear norm supremum with the same two-sided error.
Use: original matrix-budget maxima share one derived quadratic remainder.
Article: main_krylov, thm:DC, true sup-norm first-order expansion.
Proof: the attained linear maximum supplies a real source witness and
nonemptiness. Uniform norm differences bound every true nonlinear value above
and bound that witness below. Real least-upper-bound calculus gives both
supremum inequalities and hence the stated absolute error. -/
theorem sup_norm_remainder (f L : Y → F) (K : Set Y) (c r : ℝ)
    (hL : IsGreatest ((fun y => ‖L y‖) '' K) c)
    (hrem : ∀ y∈K,‖f y-L y‖≤r) :
    |sSup ((fun y => ‖f y‖) '' K)-c|≤r := by
  obtain ⟨y,hy,hvalue⟩ := hL.1
  have hupper : ∀ z∈((fun y => ‖f y‖) '' K),z≤c+r := by
    rintro z ⟨x,hx,rfl⟩
    have hl := hL.2 ⟨x,hx,rfl⟩
    have hn := norm_sub_norm_le (f x) (L x)
    have hr := hrem x hx
    linarith
  have hbdd : BddAbove ((fun y => ‖f y‖) '' K) := ⟨c+r,hupper⟩
  have hne : ((fun y => ‖f y‖) '' K).Nonempty := ⟨‖f y‖,y,hy,rfl⟩
  have hu := csSup_le hne hupper
  have hl := le_csSup hbdd (show ‖f y‖∈((fun y => ‖f y‖) '' K) from ⟨y,hy,rfl⟩)
  have hn := norm_sub_norm_le (L y) (f y)
  rw [norm_sub_rev] at hn
  have hr := hrem y hy
  change ‖L y‖=c at hvalue
  apply abs_le.mpr
  constructor <;> linarith

end
end krylov.Stability

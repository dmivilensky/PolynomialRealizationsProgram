import krylov.Convergence.OneGradientCompact

/-!
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL.
Use: obtain one true first-order change bound for the independent finite
one-gradient query fields before every compact reference family. Actual
native reference-step errors follow after genuine scalar input substitution.
Source: compact C-one mean-value bounds for the actual operator executor.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual C-one operator-policy fields have a common full first-order
input tube; the finite gradient and operator perturbations may vary together.
Article: lem:cycle-transfer, thm:V and prop:EL. -/
theorem compact_oneGradient_field_changes (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (K : Set E) (hK : IsCompact K)
    (hF : ∀ g∈K,ContDiffAt ℝ 1 (oneGradientFiniteField m Q N) (g,0)) :
    ∃ δ C : ℝ,0<δ ∧0<C ∧∀ g∈K,∀ v : E,∀ Θ : Fin N → E →L[ℝ] E,‖(v,Θ)‖≤δ →
      ‖oneGradientFiniteField m Q N (g+v,Θ)-oneGradientFiniteField m Q N (g,0)‖≤C*‖(v,Θ)‖ := by
  have hfull : ∀ z∈K×ˢ{(0 : Fin N → E →L[ℝ] E)},
      ContDiffAt ℝ 1 (oneGradientFiniteField m Q N) z := by
    rintro ⟨g,θ⟩ ⟨hg,hθ⟩
    have he : θ=0 := hθ
    subst θ
    exact hF g hg
  obtain ⟨δ,L,_,hδ,hL,_,_,hbound⟩ := compact_c1_field_bounds (oneGradientFiniteField m Q N)
    (K×ˢ{(0 : Fin N → E →L[ℝ] E)}) (hK.prod isCompact_singleton) hfull
  refine ⟨δ,L+1,hδ,by positivity,?_⟩
  intro g hg v Θ hΘ
  have hd : ‖(g+v,Θ)-(g,0)‖≤δ := by
    simpa only [Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hΘ
  have hh := (hbound (g,0) ⟨hg,rfl⟩ (g+v,Θ) hd).1
  simp only [Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : L≤L+1) (norm_nonneg _))

end
end krylov.Convergence

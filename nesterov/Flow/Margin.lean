import nesterov.Flow.Extension

/-!
Article: Lemma `extend`, its convex C¹,¹ remainder with the exact constant.
Use: export the first conclusion directly from the source margin assumptions,
for every real declared K, independently of choosing m or a larger L.
-/
namespace nesterov.Flow
noncomputable section
open scoped InnerProductSpace
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_convex_interpolant_of_margin {x G : I→E} {F : I→ℝ} {ε K : ℝ}
    (hε : 0<ε)
    (hmargin : ∀ i j,ε*‖x i-x j‖^2≤F i-F j-⟪G j,x i-x j⟫_ℝ)
    (hlip : ∀ i j,‖G i-G j‖≤K*‖x i-x j‖)
    (star : I) (hx : x star=0) (hG : G star=0) (hF : F star=0) :
    ∃ φ : E→ℝ,Differentiable ℝ φ ∧ ConvexOn ℝ Set.univ φ ∧
      (∀ u v,‖gradient φ u-gradient φ v‖≤(K^2/(2*ε))*‖u-v‖) ∧
      ∀ i,φ (x i)=F i ∧ gradient φ (x i)=G i := by
  by_cases hK : 0<K
  · let M := K^2/(2*ε)
    have hM : 0<M := by dsimp [M];positivity
    have htable : ∀ i j,F j+⟪G j,x i-x j⟫_ℝ+‖G i-G j‖^2/(2*M)≤F i := by
      intro i j
      have hs : ‖G i-G j‖^2≤K^2*‖x i-x j‖^2 := by
        have hh := (sq_le_sq₀ (norm_nonneg (G i-G j))
          (mul_nonneg hK.le (norm_nonneg (x i-x j)))).mpr (hlip i j)
        simpa only [mul_pow] using hh
      have he : (2*M)*ε=K^2 := by dsimp [M];field_simp
      have hh : ‖G i-G j‖^2/(2*M)≤ε*‖x i-x j‖^2 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
        nlinarith
      linarith [hmargin i j]
    obtain ⟨φ,hd,hco,hg,hdata⟩ := exists_convex_smooth_interpolant hM htable star hx hG hF
    exact ⟨φ,hd,convexOn_of_global_support hco,hg,hdata⟩
  · have hgzero (i : I) : G i=0 := by
      have hh := hlip i star
      rw [hG,sub_zero,hx,sub_zero] at hh
      exact norm_eq_zero.mp (le_antisymm
        (hh.trans (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hK) (norm_nonneg _))) (norm_nonneg _))
    have hxzero (i : I) : x i=0 := by
      have h₁ := hmargin i star
      have h₂ := hmargin star i
      simp only [hx,hG,hF,hgzero,sub_zero,zero_sub,inner_zero_left,norm_neg] at h₁ h₂
      have hh : ε*‖x i‖^2≤0 := by linarith
      have hs : ‖x i‖^2≤0 := le_of_not_gt
        (fun hp=>(not_lt_of_ge hh) (mul_pos hε hp))
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (x i)])
    have hfzero (i : I) : F i=0 := by
      have h₁ := hmargin i star
      have h₂ := hmargin star i
      simp only [hxzero,hgzero,hF,sub_self,norm_zero,zero_pow (by decide : 2≠0),
        mul_zero,inner_zero_left,sub_zero,zero_sub] at h₁ h₂
      linarith
    have hgrad (u : E) : gradient (fun _ : E=>(0:ℝ)) u=0 := by
      exact (hasGradientAt_const u (0:ℝ)).gradient
    refine ⟨fun _=>0,differentiable_const (0:ℝ),convexOn_const _ (convex_univ),?_,?_⟩
    · intro u v
      rw [hgrad,hgrad,sub_self,norm_zero]
      positivity
    · intro i
      simp only [hgrad,hfzero,hgzero,and_self]

end
end nesterov.Flow

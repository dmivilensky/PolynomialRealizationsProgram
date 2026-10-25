import chebyshev2.StateRegion.ArticleCoordinates

/-!
Article: chebyshev2, Lemma 8.
Proposition 12, literally at an arbitrary interior moment pair (U0,U1).
Result: `chebyshev2.StateRegion.Scales.mean_one_boundary` supplies the stated article
conclusion.
-/
namespace chebyshev2.StateRegion.Scales
noncomputable section
open Set MeasureTheory
variable (S : Scales)
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `0 < S.yPlus u t ∧ S.yPlus u t < u ∧ u < S.yMinus u t ∧ S.yMinus
u t < 1`.

Use: `chebyshev2.StateRegion.Scales.article_interior_bounds` uses this bound to establish
the bound stated in that declaration.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.article_interior_bounds`.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.k₀_pos`,
`chebyshev2.StateRegion.Scales.yPlus_den_lower`,
`chebyshev2.StateRegion.Scales.yMinus_den_lower` with the arguments shown in the proof.
-/
theorem interior_y_bounds {u t : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1) :
    0 < S.yPlus u t ∧ S.yPlus u t < u ∧ u < S.yMinus u t ∧ S.yMinus u t < 1 := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.k₀_pos`,
  -- `chebyshev2.StateRegion.Scales.yPlus_den_lower`,
  -- `chebyshev2.StateRegion.Scales.yMinus_den_lower` with the arguments shown in the
  -- proof.
  have hu' : u ∈ Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.le⟩
  have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
  have hdPlus := S.k₀_pos.trans_le (S.yPlus_den_lower hu' ht')
  have hdMinus := S.k₀_pos.trans_le (S.yMinus_den_lower hu'.2 ht'.1)
  refine ⟨div_pos (mul_pos (mul_pos S.k₁_pos hu.1) (sub_pos.mpr ht.2)) hdPlus,?_,?_,?_⟩
  · rw [yPlus,div_lt_iff₀ hdPlus]
    have hp := mul_pos (mul_pos hu.1 ht.1) (S.D_pos hu'.2)
    dsimp [D] at hp
    nlinarith
  · rw [yMinus,lt_div_iff₀ hdMinus]
    have hp := mul_pos (mul_pos ht.1 (sub_pos.mpr hu.2)) (S.D_pos hu'.2)
    dsimp [D] at hp
    nlinarith
  · rw [yMinus,div_lt_iff₀ hdMinus]
    have hp := mul_pos S.k₀_pos (mul_pos (sub_pos.mpr hu.2) (sub_pos.mpr ht.2))
    dsimp [k₀,k₁] at *
    nlinarith

/--
Defines `articleYMinus` of type `ℝ` by `(S.k₁*v-S.k₀*u)/(S.gap*v)`.

Use: `chebyshev2.StateRegion.Scales.article_interior_bounds` uses this definition to
establish the bound stated in that declaration.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.article_interior_bounds`.
-/
def articleYMinus (u v : ℝ) : ℝ := (S.k₁*v-S.k₀*u)/(S.gap*v)
/--
Defines `articleYPlus` of type `ℝ` by `S.k₁*(u-v)/(S.gap*(1-v))`.

Use: `chebyshev2.StateRegion.Scales.article_interior_bounds` uses this definition to
establish the bound stated in that declaration.

Article: chebyshev2, Lemma 8 via `chebyshev2.StateRegion.Scales.article_interior_bounds`.
-/
def articleYPlus (u v : ℝ) : ℝ := S.k₁*(u-v)/(S.gap*(1-v))

/--
Proposition 12, literally at an arbitrary interior moment pair (U0,U1).

The stated quantitative bound `(0 < S.articleYPlus u v ∧ S.articleYPlus u v < u ∧ u <
S.articleYMinus u v ∧ S.articleYMinus u v < 1) ∧ 1-(∫ w, S.g w ∂μ) ∈ Icc (S.k*(1-u)/S.E
(S.articleYPlus u v)) (1-S.k₀*u/S.E (S.articleYMinus u v))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates
`chebyshev2.StateRegion.Scales.exists_moment_parameter`,
`chebyshev2.StateRegion.Scales.interior_yPlus`,
`chebyshev2.StateRegion.Scales.interior_yMinus` with the arguments shown in the proof.
-/
theorem article_interior_bounds {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) {u v : ℝ}
    (hmean : (∫ w, w ∂μ)=u) (hsecond : (∫ w, S.f w ∂μ)=v)
    (hu : u ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (S.f u) u) :
    (0 < S.articleYPlus u v ∧ S.articleYPlus u v < u ∧ u < S.articleYMinus u v ∧
      S.articleYMinus u v < 1) ∧
    1-(∫ w, S.g w ∂μ) ∈ Icc
      (S.k*(1-u)/S.E (S.articleYPlus u v)) (1-S.k₀*u/S.E (S.articleYMinus u v)) := by
  -- Use the identities/estimates `chebyshev2.StateRegion.Scales.exists_moment_parameter`,
  -- `chebyshev2.StateRegion.Scales.interior_yPlus`,
  -- `chebyshev2.StateRegion.Scales.interior_yMinus` with the arguments shown in the proof.
  obtain ⟨t,ht,hV⟩ := S.exists_moment_parameter ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩
  have ht' : t ∈ Ioo (0:ℝ) 1 := by
    constructor
    · apply lt_of_le_of_ne ht.1
      intro he
      have ht0 : t=0 := he.symm
      simp only [ht0,V,sub_zero,one_mul,zero_mul,add_zero] at hV
      exact (ne_of_gt hv.1) hV
    · apply lt_of_le_of_ne ht.2
      intro he
      simp only [he,V,sub_self,zero_mul,one_mul,zero_add] at hV
      exact (ne_of_lt hv.2) hV
  have hyp : S.yPlus u t=S.articleYPlus u v := by
    rw [S.interior_yPlus hu ht,← hV]
    rfl
  have hym : S.yMinus u t=S.articleYMinus u v := by
    rw [S.interior_yMinus hu ht,← hV]
    rfl
  constructor
  · simpa only [hyp,hym] using S.interior_y_bounds hu ht'
  · have hf : (∫ w, S.f w ∂μ)=S.V u t := hsecond.trans hV
    simpa only [thetaMinus,thetaPlus,hyp,hym] using
      S.sharp_moment_bounds hμ ⟨hu.1.le,hu.2.le⟩ ht hmean hf

/--
Exact identity `1-(∫ w, S.g w ∂μ)=1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.two_moment_bounds`,
`chebyshev2.StateRegion.Scales.f_zero`, `chebyshev2.StateRegion.Scales.lower_boundary`
with the arguments shown in the proof.
-/
theorem mean_zero_boundary {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) (hm : (∫ w, w ∂μ)=0) :
    1-(∫ w, S.g w ∂μ)=1 := by
  have h := S.two_moment_bounds hμ
  rw [hm,S.f_zero] at h
  have hf : (∫ w, S.f w ∂μ)=S.f 0 := by rw [S.f_zero]; linarith [h.1,h.2]
  simpa [E,S.k_pos.ne'] using S.lower_boundary hμ hm hf

/--
Exact identity `1-(∫ w, S.g w ∂μ)=0`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 8.

Proof: Use the identities/estimates `chebyshev2.StateRegion.Scales.two_moment_bounds`,
`chebyshev2.StateRegion.Scales.f_one`, `chebyshev2.StateRegion.Scales.lower_boundary`
with the arguments shown in the proof.
-/
theorem mean_one_boundary {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ w ∂μ, w ∈ Icc (0:ℝ) 1) (hm : (∫ w, w ∂μ)=1) :
    1-(∫ w, S.g w ∂μ)=0 := by
  have h := S.two_moment_bounds hμ
  rw [hm,S.f_one] at h
  have hf : (∫ w, S.f w ∂μ)=S.f 1 := by rw [S.f_one]; linarith [h.1,h.2]
  simpa only [sub_self,mul_zero,zero_div] using S.lower_boundary hμ hm hf

end
end chebyshev2.StateRegion.Scales

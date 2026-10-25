import polyak.Levels.Chart.GapPolynomial

/-! The ordered real roots of the gap quadratic are constructed from its
negative value and positive endpoints, then recovered by an explicit formula. -/
noncomputable section
namespace polyak.Levels.Chart
open Set

def gapDiscriminant (C : Coefficients) : ℝ := (1-C.c1)^2+4*C.c2*(1-C.c0)
def leftRoot (C : Coefficients) : ℝ := (C.c1-1-Real.sqrt (gapDiscriminant C))/(-2*C.c2)
def rightRoot (C : Coefficients) : ℝ := (C.c1-1+Real.sqrt (gapDiscriminant C))/(-2*C.c2)

theorem gapDiscriminant_gapPolynomial (a r₁ r₂ : ℝ) :
    gapDiscriminant (gapPolynomial a r₁ r₂)=(a*(r₂-r₁))^2 := by
  dsimp [gapDiscriminant,gapPolynomial]
  ring

theorem leftRoot_gapPolynomial {a r₁ r₂ : ℝ} (ha : 0<a) (hr : r₁≤r₂) :
    leftRoot (gapPolynomial a r₁ r₂)=r₁ := by
  unfold leftRoot
  rw [gapDiscriminant_gapPolynomial,Real.sqrt_sq (mul_nonneg ha.le (sub_nonneg.mpr hr))]
  dsimp [gapPolynomial]
  field_simp
  ring

theorem rightRoot_gapPolynomial {a r₁ r₂ : ℝ} (ha : 0<a) (hr : r₁≤r₂) :
    rightRoot (gapPolynomial a r₁ r₂)=r₂ := by
  unfold rightRoot
  rw [gapDiscriminant_gapPolynomial,Real.sqrt_sq (mul_nonneg ha.le (sub_nonneg.mpr hr))]
  dsimp [gapPolynomial]
  field_simp
  ring

theorem gapPolynomial_roots_unique {a b r₁ r₂ s₁ s₂ : ℝ}
    (ha : 0<a) (hb : 0<b) (hr : r₁≤r₂) (hs : s₁≤s₂)
    (he : gapPolynomial a r₁ r₂=gapPolynomial b s₁ s₂) :
    a=b ∧ r₁=s₁ ∧ r₂=s₂ := by
  refine ⟨?_,?_,?_⟩
  · have hh := congrArg Coefficients.c2 he
    dsimp [gapPolynomial] at hh
    linarith
  · have hh := congrArg leftRoot he
    simpa only [leftRoot_gapPolynomial ha hr,leftRoot_gapPolynomial hb hs] using hh
  · have hh := congrArg rightRoot he
    simpa only [rightRoot_gapPolynomial ha hr,rightRoot_gapPolynomial hb hs] using hh

theorem exists_gap_roots (C : Coefficients) (hC : C∈CoeffDomain)
    {c₀ : ℝ} (hc₀ : c₀∈Ioo (-1:ℝ) 1) (hneg : 1+c₀<C.eval c₀) :
    ∃ r₁ r₂ : ℝ,-1<r₁ ∧ r₁<r₂ ∧ r₂<1 ∧
      C=gapPolynomial (-C.c2) r₁ r₂ ∧ amplitudeFloor r₁ r₂< -C.c2 := by
  let f := fun c : ℝ=>1+c-C.eval c
  have hcont : Continuous f := by dsimp [f,Coefficients.eval]; fun_prop
  have hl : 0<f (-1) := by dsimp [f]; linarith [hC.2.2]
  have hr : 0<f 1 := by dsimp [f]; linarith [hC.2.1]
  have hc : f c₀<0 := by dsimp [f]; linarith
  obtain ⟨r₁,hr₁,hzero₁⟩ := intermediate_value_Icc' hc₀.1.le hcont.continuousOn ⟨hc.le,hl.le⟩
  obtain ⟨r₂,hr₂,hzero₂⟩ := intermediate_value_Icc hc₀.2.le hcont.continuousOn ⟨hc.le,hr.le⟩
  have hl₁ : -1<r₁ := by
    apply lt_of_le_of_ne hr₁.1
    intro he
    rw [he,hzero₁] at hl
    exact lt_irrefl _ hl
  have hr₁c : r₁<c₀ := by
    apply lt_of_le_of_ne hr₁.2
    intro he
    rw [← he,hzero₁] at hc
    exact lt_irrefl _ hc
  have hc₂ : c₀<r₂ := by
    apply lt_of_le_of_ne hr₂.1
    intro he
    rw [he,hzero₂] at hc
    exact lt_irrefl _ hc
  have hr₂u : r₂<1 := by
    apply lt_of_le_of_ne hr₂.2
    intro he
    rw [← he,hzero₂] at hr
    exact lt_irrefl _ hr
  have hdist : r₁-r₂≠0 := ne_of_lt (by linarith)
  have hprod : (r₁-r₂)*(-C.c2*(r₁+r₂)+(1-C.c1))=0 := by
    dsimp [f,Coefficients.eval] at hzero₁ hzero₂
    linear_combination hzero₁-hzero₂
  have hlinear : -C.c2*(r₁+r₂)+(1-C.c1)=0 :=
    (mul_eq_zero.mp hprod).resolve_left hdist
  have hconstant : 1-C.c0= -C.c2*r₁*r₂ := by
    dsimp [f,Coefficients.eval] at hzero₁
    linear_combination hzero₁-r₁*hlinear
  have he : C=gapPolynomial (-C.c2) r₁ r₂ := by
    apply Coefficients.ext
    · dsimp [gapPolynomial]; linarith
    · dsimp [gapPolynomial]; linarith
    · dsimp [gapPolynomial]; ring
  refine ⟨r₁,r₂,hl₁,hr₁c.trans hc₂,hr₂u,he,?_⟩
  have hh := hC.2.1
  rw [he,gapPolynomial_one] at hh
  unfold amplitudeFloor
  apply (div_lt_iff₀ (mul_pos (by linarith : 0<1-r₁) (by linarith : 0<1-r₂))).mpr
  nlinarith

theorem continuousOn_leftRoot : ContinuousOn leftRoot {C : Coefficients | C.c2≠0} := by
  unfold leftRoot gapDiscriminant
  fun_prop (disch := intro C hC; exact mul_ne_zero (by norm_num) hC)

theorem continuousOn_rightRoot : ContinuousOn rightRoot {C : Coefficients | C.c2≠0} := by
  unfold rightRoot gapDiscriminant
  fun_prop (disch := intro C hC; exact mul_ne_zero (by norm_num) hC)

end polyak.Levels.Chart

import polyak.Levels.Chart.Homeomorphism

/-! The exact gap polynomial and the graphs of its single-harmonic tongues.
The roots and amplitude remain genuine independent real coordinates. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

def gapPolynomial (a r₁ r₂ : ℝ) : Coefficients where
  c0 := 1-a*r₁*r₂
  c1 := 1+a*(r₁+r₂)
  c2 := -a

theorem gapPolynomial_eval (a r₁ r₂ c : ℝ) :
    (gapPolynomial a r₁ r₂).eval c=1+c-a*(c-r₁)*(c-r₂) := by
  dsimp [gapPolynomial,Coefficients.eval]
  ring

def amplitudeFloor (r₁ r₂ : ℝ) : ℝ := 2/((1-r₁)*(1-r₂))

theorem amplitudeFloor_pos {r₁ r₂ : ℝ} (h₁ : r₁<1) (h₂ : r₂<1) :
    0<amplitudeFloor r₁ r₂ := div_pos (by norm_num) (mul_pos (by linarith) (by linarith))

theorem gapPolynomial_mem_domain {a r₁ r₂ : ℝ} (hl : -1<r₁)
    (hr : r₁≤r₂) (hu : r₂<1) (ha : amplitudeFloor r₁ r₂<a) :
    gapPolynomial a r₁ r₂∈CoeffDomain := by
  have h₁ : r₁<1 := hr.trans_lt hu
  have hap : 0<a := (amplitudeFloor_pos h₁ hu).trans ha
  refine ⟨by dsimp [gapPolynomial]; linarith,?_,?_⟩
  · rw [gapPolynomial_eval]
    unfold amplitudeFloor at ha
    have hh := (div_lt_iff₀ (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr hu))).mp ha
    nlinarith
  · rw [gapPolynomial_eval]
    have hh : 0<a*(1+r₁)*(1+r₂) :=
      mul_pos (mul_pos hap (by linarith)) (by linarith)
    nlinarith

theorem gapPolynomial_one {a r₁ r₂ : ℝ} :
    (gapPolynomial a r₁ r₂).eval 1=2-a*(1-r₁)*(1-r₂) := by
  rw [gapPolynomial_eval]
  ring

theorem gapPolynomial_neg_one (a r₁ r₂ : ℝ) :
    (gapPolynomial a r₁ r₂).eval (-1)= -a*(1+r₁)*(1+r₂) := by
  rw [gapPolynomial_eval]
  ring

theorem gapPolynomial_dip_iff {a r₁ r₂ c : ℝ} (ha : 0<a) (hr : r₁<r₂) :
    1+c<(gapPolynomial a r₁ r₂).eval c ↔ r₁<c ∧ c<r₂ := by
  rw [gapPolynomial_eval]
  have he : 1+c<1+c-a*(c-r₁)*(c-r₂) ↔ (c-r₁)*(c-r₂)<0 := by
    constructor
    · intro hh
      exact neg_of_mul_neg_right (by nlinarith : a*((c-r₁)*(c-r₂))<0) ha.le
    · intro hh
      have := mul_neg_of_pos_of_neg ha hh
      nlinarith
  rw [he,mul_neg_iff]
  constructor
  · rintro (⟨h₁,h₂⟩|⟨h₁,h₂⟩)
    · exact ⟨by linarith,by linarith⟩
    · exfalso; linarith
  · rintro ⟨h₁,h₂⟩
    exact Or.inl ⟨by linarith,by linarith⟩

theorem gapPolynomial_closed_dip_iff {a r₁ r₂ c : ℝ} (ha : 0<a) (hr : r₁≤r₂) :
    1+c≤(gapPolynomial a r₁ r₂).eval c ↔ r₁≤c ∧ c≤r₂ := by
  rw [gapPolynomial_eval]
  constructor
  · intro h
    have hp : (c-r₁)*(c-r₂)≤0 := by
      exact nonpos_of_mul_nonpos_right (by nlinarith : a*((c-r₁)*(c-r₂))≤0) ha
    constructor
    · by_contra hh
      have h' : c<r₁ := lt_of_not_ge hh
      exact (not_lt_of_ge hp) (mul_pos_of_neg_of_neg (by linarith) (by linarith))
    · by_contra hh
      have h' : r₂<c := lt_of_not_ge hh
      exact (not_lt_of_ge hp) (mul_pos (by linarith) (by linarith))
  · rintro ⟨h₁,h₂⟩
    have hp := mul_nonpos_of_nonneg_of_nonpos (show 0≤c-r₁ by linarith) (show c-r₂≤0 by linarith)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.le hp]

def tongueHeight (c h r₁ r₂ : ℝ) : ℝ := (h-1-c)/((c-r₁)*(r₂-c))

theorem gapPolynomial_tongue_iff {a r₁ r₂ c h : ℝ}
    (ha : 0<a) (hr : r₁<r₂) (hh : 1+c<h) :
    h≤(gapPolynomial a r₁ r₂).eval c ↔
      r₁<c ∧ c<r₂ ∧ tongueHeight c h r₁ r₂≤a := by
  constructor
  · intro hpoly
    have hi := (gapPolynomial_dip_iff ha hr).mp (hh.trans_le hpoly)
    refine ⟨hi.1,hi.2,?_⟩
    unfold tongueHeight
    apply (div_le_iff₀ (mul_pos (sub_pos.mpr hi.1) (sub_pos.mpr hi.2))).mpr
    rw [gapPolynomial_eval] at hpoly
    nlinarith
  · rintro ⟨h₁,h₂,hbound⟩
    unfold tongueHeight at hbound
    have hm := (div_le_iff₀ (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂))).mp hbound
    rw [gapPolynomial_eval]
    nlinarith

end polyak.Levels.Chart

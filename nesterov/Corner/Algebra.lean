import nesterov.Corner.Constants
import nesterov.Flow.LevelSets

/-! Polynomial forms of the corner minima and the explicit regions. -/
namespace nesterov.Corner
noncomputable section
open Set

theorem le_ratio_iff {θ a b c ξ : ℝ} (hξ : ξ≤2) :
    c≤ratio θ a b ξ ↔ 4*c*(3-ξ)≤N θ a b ξ := by
  rw [ratio,le_div_iff₀ (by nlinarith : 0<4*(3-ξ))]
  constructor <;> intro h <;> nlinarith

theorem lt_ratio_iff {θ a b c ξ : ℝ} (hξ : ξ≤2) :
    c<ratio θ a b ξ ↔ 4*c*(3-ξ)<N θ a b ξ := by
  rw [ratio,lt_div_iff₀ (by nlinarith : 0<4*(3-ξ))]
  constructor <;> intro h <;> nlinarith

theorem ratio_lt_iff {θ a b c ξ : ℝ} (hξ : ξ≤2) :
    ratio θ a b ξ<c ↔ N θ a b ξ<4*c*(3-ξ) := by
  rw [ratio,div_lt_iff₀ (by nlinarith : 0<4*(3-ξ))]
  constructor <;> intro h <;> nlinarith

theorem le_cLag_iff {θ a b c : ℝ} :
    c≤cLag θ a b ↔ ∀ ξ∈Icc (0:ℝ) 2,4*c*(3-ξ)≤N θ a b ξ := by
  constructor
  · intro h ξ hξ
    exact (le_ratio_iff hξ.2).mp (h.trans (cLag_le hξ))
  · intro h
    exact le_cLag fun ξ hξ=>(le_ratio_iff hξ.2).mpr (h ξ hξ)

theorem cDisc_lt_iff {θ a b c : ℝ} :
    cDisc θ a b<c ↔ ∃ ξ∈discreteSet,ratio θ a b ξ<c := by
  constructor
  · intro h
    obtain ⟨ξ,hξ,he⟩ := cDisc_attained θ a b
    exact ⟨ξ,hξ,he ▸ h⟩
  · rintro ⟨ξ,hξ,h⟩
    exact (cDisc_le hξ).trans_lt h

theorem uniform_tail_margin {θ a b c ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2)
    (hc : c<cLag θ a b) :
    4*(cLag θ a b-c)≤N θ a b ξ-4*c*(3-ξ) := by
  have h := (le_ratio_iff hξ.2).mp (cLag_le (θ:=θ) (a:=a) (b:=b) hξ)
  have hm : 0≤(2-ξ)*(cLag θ a b-c) := mul_nonneg (by linarith [hξ.2]) (sub_nonneg.mpr hc.le)
  nlinarith

theorem flow_difference (θ a b ξ : ℝ) :
    N θ a b ξ-4*(θ/3)*(3-ξ)=
      2*ξ*((5*θ/3-4*a)+(4*a+b-2*θ)*ξ) := by unfold N;ring

theorem alternating_difference (θ a b ξ : ℝ) :
    N θ a b ξ-4*cpi θ a b*(3-ξ)=
      2*(2-ξ)*((7*θ-12*a-6*b)-(4*a+b-2*θ)*ξ) := by unfold N cpi;ring

theorem wedge_difference (a b ξ : ℝ) :
    N 3 a b ξ-4*(3-ξ)=2*ξ*((5-4*a)+(4*a+b-6)*ξ) := by unfold N;ring

theorem affine_nonneg {A B ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2)
    (hA : 0≤A) (hB : 0≤A+2*B) : 0≤A+B*ξ := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hξ.2) hA,mul_nonneg hξ.1 hB]

theorem cQ_ge_third {θ : ℝ} (hθ : 0≤θ) (hθ3 : θ≤3) : θ/3≤Flow.cQ θ 2 := by
  apply (Flow.le_cQ_iff _ _ _).mpr
  constructor
  · linarith
  · unfold Flow.delta
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ3) (show 0≤3+θ by linarith)]

theorem flow_region_polynomial {θ a b : ℝ} (ha : a≤5*θ/12)
    (hb : 7*θ/6≤2*a+b) {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    4*(θ/3)*(3-ξ)≤N θ a b ξ := by
  have hB : 0≤(5*θ/3-4*a)+(4*a+b-2*θ)*ξ :=
    affine_nonneg hξ (by linarith) (by linarith)
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hξ.1) hB
  rw [←flow_difference] at h
  linarith

theorem flow_region_minima {θ a b : ℝ} (ha : a≤5*θ/12) (hb : 7*θ/6≤2*a+b) :
    cLag θ a b=θ/3 ∧ cDisc θ a b=θ/3 := by
  have hl : θ/3≤cLag θ a b := le_cLag_iff.mpr (fun _ hξ=>flow_region_polynomial ha hb hξ)
  have hd : cDisc θ a b≤θ/3 := (cDisc_endpoints _ _ _).trans (min_le_left _ _)
  have ho := cLag_le_cDisc θ a b
  exact ⟨le_antisymm (ho.trans hd) hl,le_antisymm hd (hl.trans ho)⟩

theorem alternating_region_polynomial {θ a b : ℝ} (hb : 2*a+b<7*θ/6)
    (hab : 5*a+2*b≤11*θ/4) {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    4*cpi θ a b*(3-ξ)≤N θ a b ξ := by
  have hB : 0≤(7*θ-12*a-6*b)-(4*a+b-2*θ)*ξ := by
    simpa only [sub_eq_add_neg,neg_mul] using
      (affine_nonneg (A:=7*θ-12*a-6*b) (B:= -(4*a+b-2*θ)) hξ (by linarith) (by linarith))
  have h := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (sub_nonneg.mpr hξ.2)) hB
  rw [←alternating_difference] at h
  linarith

theorem alternating_region_minima {θ a b : ℝ} (hb : 2*a+b<7*θ/6)
    (hab : 5*a+2*b≤11*θ/4) :
    cLag θ a b=cpi θ a b ∧ cDisc θ a b=cpi θ a b := by
  have hl : cpi θ a b≤cLag θ a b := le_cLag_iff.mpr
    (fun _ hξ=>alternating_region_polynomial hb hab hξ)
  have hd : cDisc θ a b≤cpi θ a b := (cDisc_endpoints _ _ _).trans (min_le_right _ _)
  have ho := cLag_le_cDisc θ a b
  exact ⟨le_antisymm (ho.trans hd) hl,le_antisymm hd (hl.trans ho)⟩

theorem concave_interpolation (θ a b c ξ : ℝ) :
    N θ a b ξ-4*c*(3-ξ)=
      (2-ξ)/2*(4*(θ-3*c))+ξ/2*(4*(cpi θ a b-c))-
        2*(4*a+b-2*θ)*ξ*(2-ξ) := by unfold N cpi;ring

theorem concave_region_polynomial {θ a b c : ℝ} (hconc : 4*a+b≤2*θ)
    (hflow : c≤θ/3) (hpi : c≤cpi θ a b) {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) :
    4*c*(3-ξ)≤N θ a b ξ := by
  have h0 : 0≤(2-ξ)/2*(4*(θ-3*c)) := mul_nonneg (by linarith [hξ.2]) (by linarith)
  have h2 : 0≤ξ/2*(4*(cpi θ a b-c)) := mul_nonneg (by linarith [hξ.1]) (by linarith)
  have hC : 2*(4*a+b-2*θ)*ξ*(2-ξ)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hξ.1)
      (sub_nonneg.mpr hξ.2)
  rw [←sub_nonneg,concave_interpolation]
  linarith

theorem optimal_wedge_minima {a b : ℝ} (ha : a≤5/4) (hb : 7/2≤2*a+b) :
    cLag 3 a b=1 ∧ cDisc 3 a b=1 := by
  simpa only [show (3:ℝ)/3=1 by norm_num] using
    (flow_region_minima (θ:=3) (a:=a) (b:=b) (by linarith) (by linarith))

theorem tmm_numerator (ξ : ℝ) : N 3 (5/4) 1 ξ=4*(3-ξ) := by unfold N;ring

theorem tmm_ratio {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) : ratio 3 (5/4) 1 ξ=1 := by
  unfold ratio
  rw [tmm_numerator]
  exact div_self (by nlinarith [hξ.2] : 4*(3-ξ)≠0)

end
end nesterov.Corner

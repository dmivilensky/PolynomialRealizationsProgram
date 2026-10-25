import polyak.Levels.Threshold.Kappa
import polyak.General.Regions.TongueCriteria
import polyak.Global.Threshold.GlobalStructure

/-! The explicit rational-tongue boundary in the extended condition-number
line. A nonpositive denominator has the literal value positive infinity. -/
noncomputable section
namespace polyak.Farey
open General Levels Set

def XiInfinity (y β c : ℝ) : ℝ :=
  (1-c)*(y*(1+β)-2*(1-2*β*c+β^2))/(y*(1-β))

theorem Xi_inverse_kappa (q : Tuning) (c : ℝ) :
    q.Xi c=XiInfinity q.y q.beta c-
      kappaNumerator q.y q.beta c/(q.y*(1-q.beta)*(q.kappa-1)) := by
  have hκ := ne_of_gt q.kappa_pos
  have hy := ne_of_gt q.y_pos
  have hβ := ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hκ1 := ne_of_gt (sub_pos.mpr q.kappa_gt_one)
  dsimp [Tuning.Xi,Tuning.A,Tuning.B,Tuning.x,XiInfinity,kappaNumerator]
  field_simp [hκ,hy,hβ,hκ1]
  ring

def tongueDenominator (y β c h : ℝ) : ℝ :=
  (1-c)*(y*(1+β)-2*(1-2*β*c+β^2))-h*y*(1-β)

def tongueBoundary (y β c h : ℝ) : EReal :=
  if 0<tongueDenominator y β c h then
    ((1+kappaNumerator y β c/tongueDenominator y β c h : ℝ):EReal) else ⊤

theorem Xi_ge_iff_tongue (q : Tuning) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) (h : ℝ) :
    h≤q.Xi c ↔ tongueBoundary q.y q.beta c h≤(q.kappa:EReal) := by
  have hN := kappaNumerator_pos q hc
  have hyβ : 0<q.y*(1-q.beta) := mul_pos q.y_pos (sub_pos.mpr q.beta_lt_one)
  have hκ : 0<q.kappa-1 := sub_pos.mpr q.kappa_gt_one
  have he : (q.Xi c-h)*(q.y*(1-q.beta)*(q.kappa-1))=
      tongueDenominator q.y q.beta c h*(q.kappa-1)-kappaNumerator q.y q.beta c := by
    rw [Xi_inverse_kappa]
    unfold XiInfinity tongueDenominator
    field_simp [ne_of_gt q.y_pos,ne_of_gt (sub_pos.mpr q.beta_lt_one),ne_of_gt hκ]
    ring
  have hden : 0<q.y*(1-q.beta)*(q.kappa-1) := mul_pos hyβ hκ
  by_cases hd : 0<tongueDenominator q.y q.beta c h
  · rw [tongueBoundary,ite_eq_left hd,EReal.coe_le_coe_iff]
    constructor <;> intro hh
    · have hp := mul_nonneg (sub_nonneg.mpr hh) hden.le
      have hdiv : kappaNumerator q.y q.beta c/tongueDenominator q.y q.beta c h≤q.kappa-1 :=
        (div_le_iff₀ hd).mpr (by nlinarith)
      linarith
    · have hdiv : kappaNumerator q.y q.beta c/tongueDenominator q.y q.beta c h≤q.kappa-1 := by linarith
      have hp := (div_le_iff₀ hd).mp hdiv
      apply le_of_not_gt
      intro hh'
      have := mul_neg_of_neg_of_pos (sub_neg.mpr hh') hden
      nlinarith
  · rw [tongueBoundary,ite_eq_right hd]
    have himp : ¬h≤q.Xi c := by
      intro hh
      have hh' := mul_nonneg (sub_nonneg.mpr hh) hden.le
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) hκ.le
      nlinarith
    simp only [top_le_iff,EReal.coe_ne_top,iff_false]
    exact himp

def rationalTongue (p : Global.Threshold.ParameterStrip) (j k : ℕ) : EReal :=
  let ω:=General.Regions.rationalAngle j k
  tongueBoundary p.val.1 p.val.2 (Real.cos ω)
    ((Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin ω)

theorem rational_tongue_epigraph (q : Tuning) {j k : ℕ}
    (hj : 1≤j) (hjk : 2*j<k) :
    q.angle (General.Regions.rationalAngle j k)≤Real.pi/k ↔
      rationalTongue (Global.Threshold.parameters q) j k≤(q.kappa:EReal) := by
  rw [(General.Regions.rational_angle_le_iff_explicit q hj hjk).1]
  exact Xi_ge_iff_tongue q ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩ _

theorem rationalTongue_eq_top {p : Global.Threshold.ParameterStrip} {j k : ℕ}
    (h : tongueDenominator p.val.1 p.val.2
      (Real.cos (General.Regions.rationalAngle j k))
      ((Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*
        Real.sin (General.Regions.rationalAngle j k))≤0) : rationalTongue p j k=⊤ := by
  exact ite_eq_right (not_lt_of_ge h)

end polyak.Farey

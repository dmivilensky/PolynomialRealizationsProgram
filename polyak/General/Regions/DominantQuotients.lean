import polyak.General.Regions.Quotients
import polyak.General.Regions.Radii
import polyak.General.RootsDominant

/-! Article: Corollary C(c). All root hypotheses and endpoint signs are
proved from the tuning, including equal root radii and beta=0. -/
namespace polyak.General.Regions
noncomputable section

private theorem eval_abs_nonneg {p β r : ℝ} (_hβ : 0≤β)
    (hr : rootRadius p β≤r) : 0≤r^2-|p| *r+β := by
  by_cases hd : p^2≤4*β
  · nlinarith [sq_nonneg (2*r-|p|),sq_abs p]
  · have he := rootRadius_equation (lt_of_not_ge hd)
    have hR : 0≤rootRadius p β := rootRadius_nonneg _ _
    have hp : |p|≤2*rootRadius p β := by
      simp only [rootRadius,hd,↓reduceIte]
      linarith [Real.sqrt_nonneg (p^2-4*β)]
    have hm : 0≤(r-rootRadius p β)*(r+rootRadius p β-|p|) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

private theorem eval_abs_pos {p β r : ℝ} (hβ : 0≤β)
    (hr : rootRadius p β<r) : 0<r^2-|p| *r+β := by
  by_cases hd : p^2≤4*β
  · have he : rootRadius p β=Real.sqrt β := rootRadius_eq_sqrt hd
    have hs := Real.sq_sqrt hβ
    have hb := Real.sqrt_nonneg β
    have hh : |p|≤2*Real.sqrt β := by nlinarith [sq_abs p,abs_nonneg p]
    rw [he] at hr
    have hsq : 0<(r-Real.sqrt β)^2 := sq_pos_of_pos (by linarith)
    nlinarith [mul_nonneg (by linarith : 0≤r) (show 0≤2*Real.sqrt β-|p| by linarith)]
  · have he := rootRadius_equation (lt_of_not_ge hd)
    have hR : 0≤rootRadius p β := rootRadius_nonneg _ _
    have hp : |p|≤2*rootRadius p β := by
      simp only [rootRadius,hd,↓reduceIte]
      linarith [Real.sqrt_nonneg (p^2-4*β)]
    have hm : 0<(r-rootRadius p β)*(r+rootRadius p β-|p|) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- The whole real line outside the root radius has the correct polynomial sign. -/
theorem quadratic_eval_nonneg_outside {p β r : ℝ} (hβ : 0≤β)
    (hr : rootRadius p β≤r) : 0≤r^2-p*r+β ∧ 0≤r^2+p*r+β := by
  have he := eval_abs_nonneg hβ hr
  have hr0 := (rootRadius_nonneg p β).trans hr
  constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr (le_abs_self p)),
    mul_nonneg hr0 (show 0≤|p|+p by linarith [neg_abs_le p])]

/-- A strict root-radius inequality gives a strictly positive real evaluation. -/
theorem quadratic_eval_pos_outside {p β r : ℝ} (hβ : 0≤β)
    (hr : rootRadius p β<r) : 0<r^2-p*r+β ∧ 0<r^2+p*r+β := by
  have he := eval_abs_pos hβ hr
  have hr0 := (rootRadius_nonneg p β).trans hr.le
  constructor <;> nlinarith [mul_nonneg hr0 (sub_nonneg.mpr (le_abs_self p)),
    mul_nonneg hr0 (show 0≤|p|+p by linarith [neg_abs_le p])]

/-- In the lower-curvature branch the opposite endpoint is automatically nonnegative. -/
theorem dominant_Kmu_endpoint (q : Tuning) (hab : q.rhoB≤q.rhoA) :
    0≤Kmu q q.rhoA (-1) := by
  rw [Kmu_neg_one]
  have he := (quadratic_eval_nonneg_outside q.beta_nonneg hab).2
  change 0≤q.rhoA^2+(1+q.beta-q.y)*q.rhoA+q.beta at he
  have hR : 0≤q.rhoA := rootRadius_nonneg _ _
  exact mul_nonneg (mul_nonneg (by nlinarith [sq_nonneg q.rhoA,q.beta_nonneg]) (by linarith)) he

/-- In the upper-curvature branch the opposite endpoint is strictly positive. -/
theorem dominant_KL_endpoint (q : Tuning) (hab : q.rhoA<q.rhoB) :
    0<KL q q.rhoB 1 := by
  rw [KL_one]
  have he := (quadratic_eval_pos_outside q.beta_nonneg hab).1
  change 0<q.rhoB^2-(1+q.beta-q.x)*q.rhoB+q.beta at he
  have hr : 0<q.rhoB := (rootRadius_nonneg _ _).trans_lt hab
  have hr1 : q.rhoB<1 := (le_max_right _ _).trans_lt q.rhoQ_lt_one
  exact mul_pos (mul_pos (by nlinarith [q.beta_nonneg]) (by linarith)) he

/-- At a dominant negative root, only the other endpoint needs to be tested. -/
theorem dominant_negative_cubic_iff (q : Tuning)
    (hover : Real.sqrt q.beta<q.rhoQ) (hab : q.rhoA<q.rhoB) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤q.H q.rhoB c) ↔ 0≤KL q q.rhoB (-1) := by
  obtain ⟨hr,he,_,_⟩ := q.dominant_b_root hover hab.le
  have hroot : q.rhoB^2+(1+q.beta-q.y)*q.rhoB+q.beta=0 := by
    dsimp [Tuning.b] at he
    have hh : (-q.rhoB)^2-(1+q.beta-q.y)*(-q.rhoB)+q.beta=0 := by exact_mod_cast he
    nlinarith
  rw [H_nonneg_iff_KL q hroot,KL_nonneg_iff q hr.le]
  exact and_iff_left (dominant_KL_endpoint q hab).le

/-- Thus the upper-curvature quadratic regime is exactly a single endpoint inequality. -/
theorem dominant_negative_quadratic_regime_iff (q : Tuning) (hq : OmegaOne q)
    (hover : Real.sqrt q.beta<q.rhoQ) (hab : q.rhoA<q.rhoB) :
    rOne q=q.rhoQ ↔ 0≤KL q q.rhoB (-1) := by
  rw [rOne_eq_rhoQ_iff q hq hover,show q.rhoQ=q.rhoB from max_eq_right hab.le]
  exact dominant_negative_cubic_iff q hover hab

/-- The positive-root cubic test is exactly the source convex quotient test. -/
theorem dominant_positive_cubic_iff (q : Tuning)
    (hover : Real.sqrt q.beta<q.rhoQ) (hab : q.rhoB≤q.rhoA) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤q.H q.rhoA c) ↔
      (∀ c∈Set.Icc (-1:ℝ) 1,0≤Kmu q q.rhoA c) := by
  obtain ⟨_,he⟩ := q.dominant_a_root hover hab
  have hroot : q.rhoA^2-(1+q.beta-q.x)*q.rhoA+q.beta=0 := by
    dsimp [Tuning.a] at he
    exact_mod_cast he
  exact H_nonneg_iff_Kmu q hroot

/-- The positive-root quadratic regime admits the full exact vertex/discriminant test
from Kmu_nonneg_iff; its left endpoint sign is automatic by dominant_Kmu_endpoint. -/
theorem dominant_positive_quadratic_regime_iff (q : Tuning) (hq : OmegaOne q)
    (hover : Real.sqrt q.beta<q.rhoQ) (hab : q.rhoB≤q.rhoA) :
    rOne q=q.rhoQ ↔ ∀ c∈Set.Icc (-1:ℝ) 1,0≤Kmu q q.rhoA c := by
  rw [rOne_eq_rhoQ_iff q hq hover,show q.rhoQ=q.rhoA from max_eq_left hab]
  exact dominant_positive_cubic_iff q hover hab

end
end polyak.General.Regions

import polyak.General.Roots

/-! Article: lem:dominant and the two critical damping boundaries, including β=0. -/
namespace polyak.General
noncomputable section

theorem rootRadius_gt_sqrt_iff {p β : ℝ} (hβ : 0≤β) :
    Real.sqrt β<rootRadius p β ↔ 4*β<p^2 := by
  have hle := sqrt_le_rootRadius (p:=p) hβ
  have he := rootRadius_eq_sqrt_iff (p:=p) hβ
  constructor
  · intro h
    by_contra hd
    have := he.2 (le_of_not_gt hd)
    linarith
  · intro h
    apply lt_of_le_of_ne hle
    intro heq
    have := he.1 heq.symm
    linarith

theorem rootRadius_equation {p β : ℝ} (hd : 4*β<p^2) :
    (rootRadius p β)^2-|p| *rootRadius p β+β=0 := by
  have hs := Real.sq_sqrt (show 0≤p^2-4*β by linarith)
  simp only [rootRadius,show ¬p^2≤4*β from not_le.mpr hd,↓reduceIte]
  nlinarith [sq_abs p]

namespace Tuning

theorem damping_iff (q : Tuning) : q.rhoQ=Real.sqrt q.beta ↔
    (1-Real.sqrt q.beta)^2≤q.x ∧ q.y≤(1+Real.sqrt q.beta)^2 := by
  have hs := Real.sq_sqrt q.beta_nonneg
  have hs0 := Real.sqrt_nonneg q.beta
  have hA := sqrt_le_rootRadius (p:=1+q.beta-q.x) q.beta_nonneg
  have hB := sqrt_le_rootRadius (p:=1+q.beta-q.y) q.beta_nonneg
  have heA := rootRadius_eq_sqrt_iff (p:=1+q.beta-q.x) q.beta_nonneg
  have heB := rootRadius_eq_sqrt_iff (p:=1+q.beta-q.y) q.beta_nonneg
  constructor
  · intro h
    have heA' : q.rhoA=Real.sqrt q.beta := le_antisymm
      (le_trans (le_max_left _ _) (le_of_eq h)) hA
    have heB' : q.rhoB=Real.sqrt q.beta := le_antisymm
      (le_trans (le_max_right _ _) (le_of_eq h)) hB
    have hpa := heA.1 heA'
    have hpb := heB.1 heB'
    constructor <;> nlinarith
  · intro h
    have hpa : (1+q.beta-q.x)^2≤4*q.beta := by
      have hx : 1+q.beta-q.x≤2*Real.sqrt q.beta := by nlinarith [h.1]
      have hx' : -(2*Real.sqrt q.beta)≤1+q.beta-q.x := by nlinarith [h.2,q.x_lt_y]
      nlinarith
    have hpb : (1+q.beta-q.y)^2≤4*q.beta := by
      have hy : 1+q.beta-q.y≤2*Real.sqrt q.beta := by nlinarith [h.1,q.x_lt_y]
      have hy' : -(2*Real.sqrt q.beta)≤1+q.beta-q.y := by nlinarith [h.2]
      nlinarith
    simp only [rhoQ,rhoA,rhoB,heA.2 hpa,heB.2 hpb,max_self]

theorem dominant_a_positive (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoB≤q.rhoA) : 0<1+q.beta-q.x := by
  have hq : q.rhoQ=q.rhoA := max_eq_left hab
  have hd := (rootRadius_gt_sqrt_iff q.beta_nonneg).1 (by simpa [hq,rhoA] using h)
  by_contra hp
  have hp : 1+q.beta-q.x≤0 := le_of_not_gt hp
  have hp' : 1+q.beta-q.y<0 := by linarith [q.x_lt_y]
  have hs : |1+q.beta-q.x| < |1+q.beta-q.y| := by
    rw [abs_of_nonpos hp,abs_of_neg hp']; linarith [q.x_lt_y]
  have hd' : 4*q.beta<(1+q.beta-q.y)^2 := by
    nlinarith [sq_abs (1+q.beta-q.x),sq_abs (1+q.beta-q.y),abs_nonneg (1+q.beta-q.x)]
  have := rootRadius_strict_of_abs_lt hs hd'
  exact (not_lt_of_ge hab) this

theorem dominant_b_negative (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) : 1+q.beta-q.y<0 := by
  have hq : q.rhoQ=q.rhoB := max_eq_right hab
  have hd := (rootRadius_gt_sqrt_iff q.beta_nonneg).1 (by simpa [hq,rhoB] using h)
  by_contra hp
  have hp : 0≤1+q.beta-q.y := le_of_not_gt hp
  have hp' : 0<1+q.beta-q.x := by linarith [q.x_lt_y]
  have hs : |1+q.beta-q.y| < |1+q.beta-q.x| := by
    rw [abs_of_nonneg hp,abs_of_pos hp']; linarith [q.x_lt_y]
  have hd' : 4*q.beta<(1+q.beta-q.x)^2 := by
    nlinarith [sq_abs (1+q.beta-q.x),sq_abs (1+q.beta-q.y),abs_nonneg (1+q.beta-q.y)]
  have := rootRadius_strict_of_abs_lt hs hd'
  exact (not_lt_of_ge hab) this

theorem dominant_a_root (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoB≤q.rhoA) : 0<q.rhoA ∧ q.a (q.rhoA : ℂ)=0 := by
  have hq : q.rhoQ=q.rhoA := max_eq_left hab
  have hgt : Real.sqrt q.beta<q.rhoA := by simpa [hq] using h
  have hd := (rootRadius_gt_sqrt_iff q.beta_nonneg).1 hgt
  have he := rootRadius_equation hd
  rw [abs_of_pos (q.dominant_a_positive h hab)] at he
  refine ⟨lt_of_le_of_lt (Real.sqrt_nonneg _) hgt,?_⟩
  dsimp [a]
  exact_mod_cast he

theorem dominant_b_root (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) : 0<q.rhoB ∧ q.b (-q.rhoB : ℂ)=0 ∧
      -q.rhoB < -q.beta/q.rhoB ∧ -q.beta/q.rhoB ≤ 0 := by
  have hq : q.rhoQ=q.rhoB := max_eq_right hab
  have hgt : Real.sqrt q.beta<q.rhoB := by simpa [hq] using h
  have hd := (rootRadius_gt_sqrt_iff q.beta_nonneg).1 hgt
  have he := rootRadius_equation hd
  rw [abs_of_neg (q.dominant_b_negative h hab)] at he
  have hr : 0<q.rhoB := lt_of_le_of_lt (Real.sqrt_nonneg _) hgt
  refine ⟨hr,?_,?_,?_⟩
  · dsimp [b]
    have hh : (-q.rhoB)^2-(1+q.beta-q.y)*(-q.rhoB)+q.beta=0 := by
      change q.rhoB^2-(-(1+q.beta-q.y))*q.rhoB+q.beta=0 at he
      nlinarith
    exact_mod_cast hh
  · apply (lt_div_iff₀ hr).2
    have hs := Real.sq_sqrt q.beta_nonneg
    nlinarith [Real.sqrt_nonneg q.beta]
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 q.beta_nonneg) hr.le

theorem dominant_a_factor (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoB≤q.rhoA) (z : ℂ) :
    q.a z=(z-(q.rhoA : ℂ))*(z-(q.beta/q.rhoA : ℝ)) := by
  obtain ⟨hr,hroot⟩ := q.dominant_a_root h hab
  have hRc : (q.rhoA : ℂ)≠0 := by exact_mod_cast ne_of_gt hr
  dsimp [a] at hroot ⊢
  push_cast at hroot ⊢
  field_simp [hRc]
  linear_combination z*hroot

theorem dominant_b_factor (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) (z : ℂ) :
    q.b z=(z+(q.rhoB : ℂ))*(z+(q.beta/q.rhoB : ℝ)) := by
  obtain ⟨hr,hroot,_,_⟩ := q.dominant_b_root h hab
  have hRc : (q.rhoB : ℂ)≠0 := by exact_mod_cast ne_of_gt hr
  dsimp [b] at hroot ⊢
  push_cast at hroot ⊢
  field_simp [hRc]
  linear_combination -(z*hroot)

theorem dominant_a_roots_real (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoB≤q.rhoA) {z : ℂ} (hz : q.a z=0) :
    z=(q.rhoA : ℂ) ∨ z=(q.beta/q.rhoA : ℝ) := by
  rw [q.dominant_a_factor h hab] at hz
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp
theorem dominant_b_roots_real (q : Tuning) (h : Real.sqrt q.beta<q.rhoQ)
    (hab : q.rhoA≤q.rhoB) {z : ℂ} (hz : q.b z=0) :
    z=(-q.rhoB : ℂ) ∨ z=(-q.beta/q.rhoB : ℝ) := by
  rw [q.dominant_b_factor h hab] at hz
  rcases mul_eq_zero.mp hz with h|h
  · left; linear_combination h
  · right
    have hh : z = -(↑(q.beta/q.rhoB) : ℂ) := eq_neg_of_add_eq_zero_left h
    simpa only [neg_div,Complex.ofReal_neg] using hh

end Tuning
end
end polyak.General

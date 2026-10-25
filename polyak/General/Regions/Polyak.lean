import polyak.General.Regions.Explicit
import polyak.Threshold.Parameters

/-! Article: Corollary D(a). The exact lag-one threshold and the three-cycle
condition in Polyak's original tuning, without replacing it by a rate test. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics

private theorem polyak_Xi (q : Tuning) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hx : q.x=(1-s)^2) (hy : q.y=(1+s)^2) (hb : q.beta=s^2) (c : ℝ) :
    q.Xi c=(1-c^2-((s⁻¹-s)/2)^2)/(2*((s⁻¹-s)/2)) := by
  have hsne : s≠0 := ne_of_gt hs
  have h1 : 1-s≠0 := by linarith
  have h2 : 1+s≠0 := by linarith
  dsimp [Tuning.Xi,Tuning.A,Tuning.B]
  rw [hx,hy,hb]
  field_simp [hsne,show 1-s^2≠0 by nlinarith,show (1+s)^2-(1-s)^2≠0 by nlinarith]
  ring

/-- The source completed square, valid on the entire frequency interval. -/
theorem polyak_completed_square (q : Tuning) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hx : q.x=(1-s)^2) (hy : q.y=(1+s)^2) (hb : q.beta=s^2) (c : ℝ) :
    let u := (s⁻¹-s)/2
    2*u*(1+c-q.Xi c)=(c+u)^2+2*u-1 := by
  dsimp only
  rw [polyak_Xi q hs hs1 hx hy hb]
  have hsn : s≠0 := ne_of_gt hs
  have hu : 0<(s⁻¹-s)/2 := by
    have hh : s<s⁻¹ := (mul_lt_mul_iff_left₀ hs).mp (by rw [inv_mul_cancel₀ (ne_of_gt hs)]; nlinarith)
    linarith
  field_simp [hsn,show 1-s^2≠0 by nlinarith]
  ring

/-- Strict lag-one positivity is equivalent to u>1/2, including u>1. -/
theorem polyak_mem_omegaOne_iff_u (q : Tuning) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hx : q.x=(1-s)^2) (hy : q.y=(1+s)^2) (hb : q.beta=s^2) :
    OmegaOne q ↔ (1:ℝ)/2<(s⁻¹-s)/2 := by
  let u := (s⁻¹-s)/2
  have hu : 0<u := by
    have hh : s<s⁻¹ := (mul_lt_mul_iff_left₀ hs).mp (by rw [inv_mul_cancel₀ (ne_of_gt hs)]; nlinarith)
    dsimp [u]; linarith
  have hp : 0<(q.y-q.x)*(1-q.beta) :=
    mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  have hsign (c : ℝ) : 0<q.L c ↔ 0<(c+u)^2+2*u-1 := by
    rw [q.L_eq_Xi]
    have he := polyak_completed_square q hs hs1 hx hy hb c
    change 2*u*(1+c-q.Xi c)=(c+u)^2+2*u-1 at he
    rw [mul_pos_iff_of_pos_left hp,← he,mul_pos_iff_of_pos_left (by positivity : 0<2*u)]
  constructor
  · intro h
    by_cases hu1 : u≤1
    · have hh := (hsign (-u)).mp (h (-u) (by constructor <;> linarith))
      dsimp only [u] at *
      nlinarith
    · change 1/2<u
      linarith
  · intro h c _
    apply (hsign c).mpr
    change 1/2<u at h
    nlinarith [sq_nonneg (c+u)]

/-- Three-cycle language is exactly the reverse weak inequality. -/
theorem polyak_three_tongue_iff_u (q : Tuning) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hx : q.x=(1-s)^2) (hy : q.y=(1+s)^2) (hb : q.beta=s^2) :
    q.L (-(1:ℝ)/2)≤0 ↔ (s⁻¹-s)/2≤(1:ℝ)/2 := by
  let u := (s⁻¹-s)/2
  have hu : 0<u := by
    have hh : s<s⁻¹ := (mul_lt_mul_iff_left₀ hs).mp (by rw [inv_mul_cancel₀ (ne_of_gt hs)]; nlinarith)
    dsimp [u]; linarith
  have hp : 0<(q.y-q.x)*(1-q.beta) :=
    mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  rw [q.L_eq_Xi]
  simp only [mul_nonpos_iff,hp.le,not_le.mpr hp,true_and,false_and,or_false]
  have he := polyak_completed_square q hs hs1 hx hy hb (-(1:ℝ)/2)
  change 2*u*(1+ -(1:ℝ)/2-q.Xi (-(1:ℝ)/2))=(-(1:ℝ)/2+u)^2+2*u-1 at he
  change _ ↔ u≤1/2
  have hf : (-(1:ℝ)/2+u)^2+2*u-1=(u+3/2)*(u-1/2) := by ring
  rw [hf] at he
  constructor
  · intro h
    have hh : (u+3/2)*(u-1/2)≤0 := by rw [← he]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    nlinarith
  · intro h
    have hh : (u+3/2)*(u-1/2)≤0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    rw [← he] at hh
    exact nonpos_of_mul_nonpos_right hh (by positivity)

private theorem u_gt_half_iff {s : ℝ} (hs : 0<s) :
    (1:ℝ)/2<(s⁻¹-s)/2 ↔ s<Threshold.criticalQ := by
  have hqc := Threshold.criticalQ_pos
  have he := Threshold.criticalQ_sq_add
  have hi : s*s⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hs)
  constructor
  · intro h
    have hm := mul_lt_mul_of_pos_left h hs
    nlinarith
  · intro h
    have hh : 0<(Threshold.criticalQ-s)*(Threshold.criticalQ+s+1) :=
      mul_pos (by linarith) (by linarith)
    have hval : 0<s*(s⁻¹-s-1) := by nlinarith
    have hp : 0<s⁻¹-s-1 := (mul_pos_iff_of_pos_left hs).mp hval
    linarith

/-- Generic Polyak source coordinates have exactly the critical-Q threshold. -/
theorem polyak_mem_omegaOne_iff_q (q : Tuning) {s : ℝ} (hs : 0<s) (hs1 : s<1)
    (hx : q.x=(1-s)^2) (hy : q.y=(1+s)^2) (hb : q.beta=s^2) :
    OmegaOne q ↔ s<Threshold.criticalQ :=
  (polyak_mem_omegaOne_iff_u q hs hs1 hx hy hb).trans (u_gt_half_iff hs)

/-- Polyak's actual tuning, as a point of the same relative parameter domain. -/
def polyakTuning {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) : Tuning :=
  Tuning.ofOriginal μ L (polyakAlpha μ L) (polyakBeta μ L) hμ hL
    (polyakAlpha_pos hμ hL) (polyakBeta_mem hμ hL).1 (polyakBeta_mem hμ hL).2
    (polyak_quadratic_condition hμ hL).2

theorem polyakTuning_coordinates {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    (polyakTuning hμ hL).x=(1-polyakQ μ L)^2 ∧
    (polyakTuning hμ hL).y=(1+polyakQ μ L)^2 ∧
    (polyakTuning hμ hL).beta=(polyakQ μ L)^2 := by
  have hx : (polyakTuning hμ hL).x=polyakAlpha μ L*μ := Tuning.ofOriginal_x ..
  have hA := polyak_normalizedA hμ hL
  have hB := polyak_normalizedB hμ hL
  dsimp [normalizedA,normalizedB,polyakBeta] at hA hB
  constructor
  · rw [hx]
    nlinarith
  · constructor
    · change polyakAlpha μ L*L=(1+polyakQ μ L)^2
      nlinarith
    · rfl

/-- Corollary D(a), the exact lag-one threshold in the original condition number. -/
theorem polyak_mem_omegaOne_iff_condition {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    OmegaOne (polyakTuning hμ hL) ↔ L/μ<Threshold.criticalKappa := by
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  rw [polyak_mem_omegaOne_iff_q _ (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hx hy hb,
    polyakQ_eq_conditionQ hμ hL]
  exact Threshold.conditionQ_lt_critical_iff ((one_lt_div hμ).mpr hL)

/-- The three-tongue includes the critical boundary and all supercritical Polyak tunings. -/
theorem polyak_three_tongue_iff_condition {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) :
    (polyakTuning hμ hL).L (-(1:ℝ)/2)≤0 ↔ Threshold.criticalKappa≤L/μ := by
  obtain ⟨hx,hy,hb⟩ := polyakTuning_coordinates hμ hL
  rw [polyak_three_tongue_iff_u _ (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hx hy hb,
    ← not_lt,← polyak_mem_omegaOne_iff_u _ (polyakQ_pos hμ hL) (polyakQ_lt_one hμ hL) hx hy hb,
    polyak_mem_omegaOne_iff_condition hμ hL,not_lt]

end
end polyak.General.Regions

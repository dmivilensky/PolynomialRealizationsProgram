import polyak.General.Cubic
import polyak.General.Factor
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Article: def:angle and lem:angle. A continuous closed-interval angle,
defined from the source quadratic; the normalization never vanishes. -/
namespace polyak.General
noncomputable section
namespace Tuning

theorem Xi_one_neg (q : Tuning) : q.Xi 1<0 := by
  have he := q.L_eq_Xi 1
  rw [q.L_one] at he
  have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.2 q.x_lt_y) (sub_pos.2 q.beta_lt_one)
  have hx := mul_pos q.x_pos q.y_pos
  nlinarith
theorem Xi_neg_one_neg (q : Tuning) : q.Xi (-1)<0 := by
  have he := q.L_eq_Xi (-1)
  have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.2 q.x_lt_y) (sub_pos.2 q.beta_lt_one)
  nlinarith [q.L_neg_one_pos]

theorem Xi_concave (q : Tuning) : ConcaveOn ℝ Set.univ q.Xi := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hd : 0<2*q.B*(1-q.beta) := by positivity [q.B_pos,q.beta_lt_one]
  have he : q.Xi (a*x+b*y) - (a*q.Xi x+b*q.Xi y) =
      4*q.beta*a*b*(x-y)^2/(2*q.B*(1-q.beta)) := by
    have hb' : b=1-a := by linarith
    rw [hb']
    dsimp [Xi]
    field_simp
    ring
  have hp : 0≤4*q.beta*a*b*(x-y)^2/(2*q.B*(1-q.beta)) := by positivity [q.beta_nonneg]
  linarith

def angleRadius (q : Tuning) (ω : ℝ) : ℝ :=
  Real.sqrt ((q.Xi (Real.cos ω))^2+(Real.sin ω)^2)
def angle (q : Tuning) (ω : ℝ) : ℝ :=
  Real.arccos (q.Xi (Real.cos ω)/q.angleRadius ω)

theorem angleRadius_pos (q : Tuning) {ω : ℝ} (hω : ω ∈ Set.Icc 0 Real.pi) :
    0<q.angleRadius ω := by
  apply Real.sqrt_pos.2
  rcases eq_or_lt_of_le hω.1 with h|h
  · subst ω
    simp only [Real.cos_zero,Real.sin_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero]
    exact sq_pos_of_neg q.Xi_one_neg
  · rcases eq_or_lt_of_le hω.2 with h'|h'
    · subst ω
      simp only [Real.cos_pi,Real.sin_pi,zero_pow (by norm_num : 2 ≠ 0),add_zero]
      exact sq_pos_of_neg q.Xi_neg_one_neg
    · have hs := Real.sin_pos_of_pos_of_lt_pi h h'
      nlinarith [sq_nonneg (q.Xi (Real.cos ω)),sq_pos_of_pos hs,Real.sqrt_nonneg ((q.Xi (Real.cos ω))^2+(Real.sin ω)^2)]

theorem abs_Xi_le_angleRadius (q : Tuning) (ω : ℝ) :
    |q.Xi (Real.cos ω)|≤q.angleRadius ω := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Real.sin ω),sq_abs (q.Xi (Real.cos ω))]

theorem angle_continuousOn (q : Tuning) : ContinuousOn q.angle (Set.Icc 0 Real.pi) := by
  apply Real.continuous_arccos.comp_continuousOn
  apply ContinuousOn.div _ _ (fun ω hω => ne_of_gt (q.angleRadius_pos hω))
  · dsimp [Xi]; fun_prop
  · dsimp [angleRadius,Xi]; fun_prop

theorem angle_zero (q : Tuning) : q.angle 0=Real.pi := by
  dsimp [angle,angleRadius]
  rw [Real.cos_zero,Real.sin_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs,
    abs_of_neg q.Xi_one_neg]
  rw [div_neg_eq_neg_div,div_self (ne_of_lt q.Xi_one_neg),Real.arccos_neg_one]

theorem angle_pi (q : Tuning) : q.angle Real.pi=Real.pi := by
  dsimp [angle,angleRadius]
  rw [Real.cos_pi,Real.sin_pi,zero_pow (by norm_num : 2 ≠ 0),add_zero,Real.sqrt_sq_eq_abs,
    abs_of_neg q.Xi_neg_one_neg]
  rw [div_neg_eq_neg_div,div_self (ne_of_lt q.Xi_neg_one_neg),Real.arccos_neg_one]

theorem angle_mem (q : Tuning) {ω : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) :
    q.angle ω ∈ Set.Ioo 0 Real.pi := by
  have hR := q.angleRadius_pos ⟨hω.1.le,hω.2.le⟩
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hsq := Real.sq_sqrt (show 0≤(q.Xi (Real.cos ω))^2+(Real.sin ω)^2 by positivity)
  have hlt : |q.Xi (Real.cos ω)|<q.angleRadius ω := by
    change |q.Xi (Real.cos ω)|<Real.sqrt _
    nlinarith [sq_abs (q.Xi (Real.cos ω)),abs_nonneg (q.Xi (Real.cos ω)),sq_pos_of_pos hs,Real.sqrt_nonneg ((q.Xi (Real.cos ω))^2+(Real.sin ω)^2)]
  have hquot := (abs_lt.mp hlt)
  exact ⟨Real.arccos_pos.2 ((div_lt_one hR).2 hquot.2),
    Real.arccos_lt_pi.2 ((lt_div_iff₀ hR).2 (by linarith))⟩

theorem cos_angle (q : Tuning) {ω : ℝ} (hω : ω ∈ Set.Icc 0 Real.pi) :
    Real.cos (q.angle ω)=q.Xi (Real.cos ω)/q.angleRadius ω := by
  have hR := q.angleRadius_pos hω
  apply Real.cos_arccos
  · exact (le_div_iff₀ hR).2 (by linarith [(abs_le.mp (q.abs_Xi_le_angleRadius ω)).1])
  · exact (div_le_one hR).2 (le_trans (le_abs_self _) (q.abs_Xi_le_angleRadius ω))

theorem sin_angle (q : Tuning) {ω : ℝ} (hω : ω ∈ Set.Icc 0 Real.pi) :
    Real.sin (q.angle ω)=Real.sin ω/q.angleRadius ω := by
  have hR := q.angleRadius_pos hω
  have hs : 0≤Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω.1 hω.2
  have hangle : 0≤Real.sin (q.angle ω) := Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have h := Real.sin_sq_add_cos_sq (q.angle ω)
  rw [q.cos_angle hω] at h
  have hsq : (q.angleRadius ω)^2=(q.Xi (Real.cos ω))^2+(Real.sin ω)^2 :=
    Real.sq_sqrt (by positivity)
  have he : (Real.sin (q.angle ω))^2=(Real.sin ω/q.angleRadius ω)^2 := by
    field_simp at h ⊢
    nlinarith
  nlinarith [div_nonneg hs hR.le]

theorem cot_angle (q : Tuning) {ω : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) :
    Real.cos (q.angle ω)/Real.sin (q.angle ω)=q.Xi (Real.cos ω)/Real.sin ω := by
  rw [q.cos_angle ⟨hω.1.le,hω.2.le⟩,q.sin_angle ⟨hω.1.le,hω.2.le⟩]
  field_simp [ne_of_gt (q.angleRadius_pos ⟨hω.1.le,hω.2.le⟩)]

end Tuning
end
end polyak.General

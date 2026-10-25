import polyak.Levels.Chart.NormalizedInverse

/-! Constructing the unique admissible positive-momentum tuning from Ξ. -/
noncomputable section
namespace polyak.Levels.Chart
open General

def inverseBeta (C : CoefficientPoint) : ℝ := (normalizedU C-1)/(normalizedU C+1)
def inverseA (C : CoefficientPoint) : ℝ := (1-inverseBeta C)*normalizedA C
def inverseB (C : CoefficientPoint) : ℝ := (1-inverseBeta C)*normalizedB C
def inverseX (C : CoefficientPoint) : ℝ := 1+inverseBeta C-inverseA C-inverseB C
def inverseY (C : CoefficientPoint) : ℝ := 1+inverseBeta C-inverseA C+inverseB C

theorem inverseBeta_pos (C : CoefficientPoint) : 0< inverseBeta C :=
  div_pos (sub_pos.mpr (one_lt_normalizedU C)) (by linarith [one_lt_normalizedU C])

theorem inverseBeta_lt_one (C : CoefficientPoint) : inverseBeta C<1 := by
  apply (div_lt_one (by linarith [one_lt_normalizedU C])).mpr
  linarith

theorem inverse_normalization (C : CoefficientPoint) :
    (1-inverseBeta C)*normalizedU C=1+inverseBeta C := by
  unfold inverseBeta
  field_simp [show normalizedU C+1≠0 by linarith [one_lt_normalizedU C]]
  ring

theorem inverseB_pos (C : CoefficientPoint) : 0< inverseB C :=
  mul_pos (sub_pos.mpr (inverseBeta_lt_one C)) (normalizedB_pos C)

theorem inverse_stable (C : CoefficientPoint) :
    |inverseA C|+inverseB C<1+inverseBeta C := by
  have hg := mul_lt_mul_of_pos_left (normalized_stable C) (sub_pos.mpr (inverseBeta_lt_one C))
  rw [mul_add,inverse_normalization] at hg
  simpa only [inverseA,inverseB,abs_mul,abs_of_pos (sub_pos.mpr (inverseBeta_lt_one C))] using hg

theorem inverseX_pos (C : CoefficientPoint) : 0< inverseX C := by
  have hs := inverse_stable C
  have ha := le_abs_self (inverseA C)
  unfold inverseX
  linarith

theorem inverseX_lt_inverseY (C : CoefficientPoint) : inverseX C< inverseY C := by
  dsimp [inverseX,inverseY]
  linarith [inverseB_pos C]

theorem inverseY_lt (C : CoefficientPoint) : inverseY C<2*(1+inverseBeta C) := by
  have hs := inverse_stable C
  have ha := neg_abs_le (inverseA C)
  unfold inverseY
  linarith

def inverseTuning (C : CoefficientPoint) : Tuning :=
  Tuning.ofOriginal (inverseX C) (inverseY C) 1 (inverseBeta C)
    (inverseX_pos C) (inverseX_lt_inverseY C) (by norm_num) (inverseBeta_pos C).le
    (inverseBeta_lt_one C) (by simpa using inverseY_lt C)

@[simp] theorem inverseTuning_beta (C : CoefficientPoint) : (inverseTuning C).beta=inverseBeta C := rfl
@[simp] theorem inverseTuning_y (C : CoefficientPoint) : (inverseTuning C).y=inverseY C := by
  change 1*inverseY C=inverseY C
  ring
@[simp] theorem inverseTuning_x (C : CoefficientPoint) : (inverseTuning C).x=inverseX C := by
  simpa only [inverseTuning,one_mul] using Tuning.ofOriginal_x (inverseX C) (inverseY C) 1 (inverseBeta C)
    (inverseX_pos C) (inverseX_lt_inverseY C) (by norm_num) (inverseBeta_pos C).le
    (inverseBeta_lt_one C) (by simpa using inverseY_lt C)

@[simp] theorem inverseTuning_A (C : CoefficientPoint) : (inverseTuning C).A=inverseA C := by
  rw [Tuning.A,inverseTuning_x,inverseTuning_y,inverseTuning_beta]
  dsimp [inverseX,inverseY]
  ring
@[simp] theorem inverseTuning_B (C : CoefficientPoint) : (inverseTuning C).B=inverseB C := by
  rw [Tuning.B,inverseTuning_x,inverseTuning_y]
  dsimp [inverseX,inverseY]
  ring

theorem coefficients_inverseTuning (C : CoefficientPoint) : coefficients (inverseTuning C)=C.val := by
  have hD : 1-inverseBeta C≠0 := ne_of_gt (sub_pos.mpr (inverseBeta_lt_one C))
  have hw : normalizedB C≠0 := ne_of_gt (normalizedB_pos C)
  have hu := inverse_normalization C
  have hbeta : 4*inverseBeta C=(1-inverseBeta C)^2*(normalizedU C^2-1) := by
    have hs := congrArg (fun z : ℝ=>z^2) hu
    nlinarith
  apply Coefficients.ext
  · change ((inverseTuning C).B^2-(1-(inverseTuning C).beta)^2-(inverseTuning C).A^2)/
      (2*(inverseTuning C).B*(1-(inverseTuning C).beta))=C.val.c0
    rw [inverseTuning_A,inverseTuning_B,inverseTuning_beta]
    apply (div_eq_iff (by positivity [inverseB_pos C,inverseBeta_lt_one C])).mpr
    have h0 := normalized_constant_identity C
    dsimp [inverseA,inverseB]
    linear_combination -(1-inverseBeta C)^2*h0
  · change (2*(inverseTuning C).A*(1+(inverseTuning C).beta))/
      (2*(inverseTuning C).B*(1-(inverseTuning C).beta))=C.val.c1
    rw [inverseTuning_A,inverseTuning_B,inverseTuning_beta]
    apply (div_eq_iff (by positivity [inverseB_pos C,inverseBeta_lt_one C])).mpr
    have h1 := normalizedA_identity C
    dsimp [inverseA,inverseB]
    rw [← hu]
    linear_combination 2*(1-inverseBeta C)^2*h1
  · change -4*(inverseTuning C).beta/(2*(inverseTuning C).B*(1-(inverseTuning C).beta))=C.val.c2
    rw [inverseTuning_B,inverseTuning_beta]
    apply (div_eq_iff (by positivity [inverseB_pos C,inverseBeta_lt_one C])).mpr
    have h2 := normalized_quadratic_identity C
    rw [eq_div_iff (by positivity [normalizedB_pos C])] at h2
    dsimp [inverseB]
    linear_combination -(1-inverseBeta C)^2*h2-hbeta

theorem inverseTuning_eval (C : CoefficientPoint) (c : ℝ) : (inverseTuning C).Xi c=C.val.eval c := by
  rw [← eval_coefficients,coefficients_inverseTuning]

end polyak.Levels.Chart

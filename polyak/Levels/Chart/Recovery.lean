import polyak.Levels.Chart.Inverse

/-! The algebraic inverse also recovers each original tuning. This proves
injectivity directly, without assuming a labelling of the quartic roots. -/
noncomputable section
namespace polyak.Levels.Chart
open General

def coefficientPoint (q : Tuning) (hb : 0<q.beta) : CoefficientPoint :=
  ⟨coefficients q,coefficients_mem q hb⟩

theorem stableRoot_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    stableRoot (coefficientPoint q hb)=(1+q.beta)^2/((1-q.beta)*q.B) := by
  let C := coefficientPoint q hb
  let d := (1+q.beta)^2/((1-q.beta)*q.B)
  have hD : 0<1-q.beta := sub_pos.mpr q.beta_lt_one
  have hU : 0<1+q.beta := by linarith [q.beta_nonneg]
  have hB := q.B_pos
  have hda : d-2*(-C.val.c2)=(1-q.beta)/q.B := by
    dsimp [d,C,coefficientPoint,coefficients]
    field_simp
    ring
  have hda' : 2*(-C.val.c2)<d := by
    have hh := div_pos hD hB
    rw [← hda] at hh
    linarith
  have hc1 : |C.val.c1|=|q.A| *(1+q.beta)/((1-q.beta)*q.B) := by
    dsimp [C,coefficientPoint,coefficients]
    rw [abs_div,abs_mul,abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_pos hU,abs_of_pos hB,abs_of_pos hD]
    field_simp
  have hdv : |C.val.c1|<d := by
    rw [hc1]
    apply (div_lt_div_iff_of_pos_right (mul_pos hD hB)).mpr
    have hh := q.abs_A_add_B_lt
    nlinarith
  have hsec : secular (-C.val.c2) C.val.c1 (-C.val.c2-C.val.c0) d=0 := by
    unfold secular
    rw [hda]
    dsimp [d,C,coefficientPoint,coefficients]
    field_simp
    ring
  have he := (secular_exists_unique (a:= -C.val.c2) (v:=C.val.c1)
    (t:= -C.val.c2-C.val.c0) (neg_pos.mpr C.property.1)
    (by linarith [coefficient_domain_endpoint C.val C.property])).choose_spec.2 d ⟨hda',hdv,hsec⟩
  exact he.symm

theorem normalizedB_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    normalizedB (coefficientPoint q hb)=q.B/(1-q.beta) := by
  unfold normalizedB
  have hd : stableRoot (coefficientPoint q hb)+2*(coefficientPoint q hb).val.c2=
      (1-q.beta)/q.B := by
    rw [stableRoot_coefficientPoint]
    dsimp [coefficientPoint,coefficients]
    field_simp [q.B_ne_zero,ne_of_gt (sub_pos.mpr q.beta_lt_one)]
    ring
  rw [hd,one_div_div]

theorem normalizedU_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    normalizedU (coefficientPoint q hb)=(1+q.beta)/(1-q.beta) := by
  have hs := normalizedU_sq (coefficientPoint q hb)
  rw [stableRoot_coefficientPoint,normalizedB_coefficientPoint] at hs
  have he : (1+q.beta)^2/((1-q.beta)*q.B)*(q.B/(1-q.beta))=
      ((1+q.beta)/(1-q.beta))^2 := by
    field_simp [q.B_ne_zero,ne_of_gt (sub_pos.mpr q.beta_lt_one)]
  rw [he] at hs
  exact (sq_eq_sq₀ (le_of_lt (zero_lt_one.trans (one_lt_normalizedU _)))
    (by positivity [q.beta_nonneg,q.beta_lt_one])).mp hs

theorem normalizedA_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    normalizedA (coefficientPoint q hb)=q.A/(1-q.beta) := by
  unfold normalizedA
  rw [normalizedB_coefficientPoint,normalizedU_coefficientPoint]
  dsimp [coefficientPoint,coefficients]
  field_simp [q.B_ne_zero,ne_of_gt (sub_pos.mpr q.beta_lt_one),
    show 1+q.beta≠0 by linarith [q.beta_nonneg]]

theorem inverseBeta_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    inverseBeta (coefficientPoint q hb)=q.beta := by
  unfold inverseBeta
  rw [normalizedU_coefficientPoint]
  field_simp [ne_of_gt (sub_pos.mpr q.beta_lt_one)]
  ring

theorem inverseTuning_coefficientPoint (q : Tuning) (hb : 0<q.beta) :
    inverseTuning (coefficientPoint q hb)=q := by
  have hbeta := inverseBeta_coefficientPoint q hb
  have hA : inverseA (coefficientPoint q hb)=q.A := by
    rw [inverseA,hbeta,normalizedA_coefficientPoint]
    field_simp [ne_of_gt (sub_pos.mpr q.beta_lt_one)]
  have hB : inverseB (coefficientPoint q hb)=q.B := by
    rw [inverseB,hbeta,normalizedB_coefficientPoint]
    field_simp [ne_of_gt (sub_pos.mpr q.beta_lt_one)]
  have hx : inverseX (coefficientPoint q hb)=q.x := by
    rw [inverseX,hbeta,hA,hB]
    linarith [q.A_add_B]
  have hy : inverseY (coefficientPoint q hb)=q.y := by
    rw [inverseY,hbeta,hA,hB]
    have hh := q.A_sub_B
    linarith
  cases he : inverseTuning (coefficientPoint q hb) with
  | mk κ y β hκ hβ hβ1 hy0 hy1 =>
    have hxeq := inverseTuning_x (coefficientPoint q hb)
    have hyeq := inverseTuning_y (coefficientPoint q hb)
    have hbeq := inverseTuning_beta (coefficientPoint q hb)
    rw [he,hx] at hxeq
    rw [he,hy] at hyeq
    rw [he,hbeta] at hbeq
    dsimp [Tuning.x] at hxeq
    dsimp at hyeq hbeq
    subst y β
    have hk : κ=q.kappa := by
      have hqk := q.kappa_pos
      have hκ0 : 0<κ := zero_lt_one.trans hκ
      apply (mul_left_cancel₀ (ne_of_gt q.y_pos))
      have hh := (div_eq_div_iff (ne_of_gt hκ0) (ne_of_gt hqk)).mp hxeq
      linarith
    subst κ
    cases q
    rfl

end polyak.Levels.Chart

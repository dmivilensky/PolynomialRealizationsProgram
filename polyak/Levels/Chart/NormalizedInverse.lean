import polyak.Levels.Chart.ScalarRoot

/-! The actual stable branch reconstructed from arbitrary admissible Ξ
coefficients. All positivity and stability inequalities are consequences of
the coefficient domain and the proved secular equation. -/
noncomputable section
namespace polyak.Levels.Chart
open Set

abbrev CoefficientPoint := {C : Coefficients // C∈CoeffDomain}

def stableRoot (C : CoefficientPoint) : ℝ :=
  (secular_exists_unique (a:= -C.val.c2) (v:=C.val.c1) (t:= -C.val.c2-C.val.c0)
    (neg_pos.mpr C.property.1) (by linarith [coefficient_domain_endpoint C.val C.property])).choose

theorem stableRoot_spec (C : CoefficientPoint) :
    -2*C.val.c2<stableRoot C ∧ |C.val.c1|<stableRoot C ∧
      secular (-C.val.c2) C.val.c1 (-C.val.c2-C.val.c0) (stableRoot C)=0 := by
  simpa only [stableRoot,mul_neg,neg_mul] using
    (secular_exists_unique (a:= -C.val.c2) (v:=C.val.c1) (t:= -C.val.c2-C.val.c0)
      (neg_pos.mpr C.property.1) (by linarith [coefficient_domain_endpoint C.val C.property])).choose_spec.1

def normalizedB (C : CoefficientPoint) : ℝ := 1/(stableRoot C+2*C.val.c2)
def normalizedU (C : CoefficientPoint) : ℝ := Real.sqrt (stableRoot C*normalizedB C)
def normalizedA (C : CoefficientPoint) : ℝ := C.val.c1*normalizedB C/normalizedU C

theorem normalizedB_pos (C : CoefficientPoint) : 0<normalizedB C := by
  unfold normalizedB
  exact one_div_pos.mpr (by linarith [(stableRoot_spec C).1])

theorem normalizedB_identity (C : CoefficientPoint) :
    (stableRoot C+2*C.val.c2)*normalizedB C=1 :=
  mul_one_div_cancel (by linarith [(stableRoot_spec C).1])

theorem stableRoot_pos (C : CoefficientPoint) : 0<stableRoot C :=
  (abs_nonneg _).trans_lt (stableRoot_spec C).2.1

theorem normalizedU_sq (C : CoefficientPoint) :
    normalizedU C^2=stableRoot C*normalizedB C :=
  Real.sq_sqrt (mul_nonneg (stableRoot_pos C).le (normalizedB_pos C).le)

theorem one_lt_normalizedU (C : CoefficientPoint) : 1<normalizedU C := by
  have hs := normalizedU_sq C
  have hb := normalizedB_identity C
  have hp : 0< -2*C.val.c2*normalizedB C :=
    mul_pos (by linarith [C.property.1]) (normalizedB_pos C)
  have hu : 0≤normalizedU C := Real.sqrt_nonneg _
  nlinarith

theorem normalizedA_identity (C : CoefficientPoint) :
    normalizedA C*normalizedU C=C.val.c1*normalizedB C := by
  exact div_mul_cancel₀ _ (ne_of_gt (zero_lt_one.trans (one_lt_normalizedU C)))

theorem normalizedA_sq (C : CoefficientPoint) :
    normalizedA C^2*stableRoot C=C.val.c1^2*normalizedB C := by
  have h := congrArg (fun z : ℝ=>z^2) (normalizedA_identity C)
  rw [mul_pow,mul_pow,normalizedU_sq] at h
  have he : (normalizedA C^2*stableRoot C-C.val.c1^2*normalizedB C)*normalizedB C=0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (ne_of_gt (normalizedB_pos C)))

theorem normalized_constant_identity (C : CoefficientPoint) :
    2*C.val.c0*normalizedB C=normalizedB C^2-1-normalizedA C^2 := by
  have hsec := (stableRoot_spec C).2.2
  dsimp [secular] at hsec
  have hden : stableRoot C-2*(-C.val.c2)=stableRoot C+2*C.val.c2 := by ring
  rw [hden] at hsec
  change stableRoot C+C.val.c1^2/stableRoot C-2*(-C.val.c2-C.val.c0)-
    normalizedB C=0 at hsec
  have hmul := congrArg (fun z : ℝ=>z*normalizedB C) hsec
  have hdiv : C.val.c1^2/stableRoot C*normalizedB C=normalizedA C^2 := by
    rw [div_mul_eq_mul_div]
    exact (div_eq_iff (ne_of_gt (stableRoot_pos C))).mpr (normalizedA_sq C).symm
  have hid := normalizedB_identity C
  linear_combination hmul-hid-hdiv

theorem normalized_linear_identity (C : CoefficientPoint) :
    C.val.c1=normalizedA C*normalizedU C/normalizedB C := by
  rw [normalizedA_identity]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (normalizedB_pos C))).symm

theorem normalized_quadratic_identity (C : CoefficientPoint) :
    C.val.c2= -(normalizedU C^2-1)/(2*normalizedB C) := by
  apply (eq_div_iff (by positivity [normalizedB_pos C])).mpr
  have hs := normalizedU_sq C
  have hb := normalizedB_identity C
  nlinarith

theorem normalized_stable (C : CoefficientPoint) :
    |normalizedA C|+normalizedB C<normalizedU C := by
  have hw := normalizedB_pos C
  have hu : 0<normalizedU C := zero_lt_one.trans (one_lt_normalizedU C)
  have hvu : |normalizedA C| *normalizedU C=|C.val.c1| *normalizedB C := by
    calc
      _=|normalizedA C*normalizedU C| := by rw [abs_mul,abs_of_pos hu]
      _=_ := by rw [normalizedA_identity,abs_mul,abs_of_pos hw]
  have hav : |normalizedA C|<normalizedU C := by
    have hg := mul_lt_mul_of_pos_right (stableRoot_spec C).2.1 hw
    rw [← hvu,← normalizedU_sq] at hg
    nlinarith
  have hplus : 2*normalizedB C*C.val.eval 1=
      normalizedB C^2-(normalizedU C-normalizedA C)^2 := by
    dsimp [Coefficients.eval]
    have h0 := normalized_constant_identity C
    have h1 := normalizedA_identity C
    have h2 := normalized_quadratic_identity C
    rw [eq_div_iff (by positivity [normalizedB_pos C])] at h2
    nlinarith
  have hminus : 2*normalizedB C*C.val.eval (-1)=
      normalizedB C^2-(normalizedU C+normalizedA C)^2 := by
    dsimp [Coefficients.eval]
    have h0 := normalized_constant_identity C
    have h1 := normalizedA_identity C
    have h2 := normalized_quadratic_identity C
    rw [eq_div_iff (by positivity [normalizedB_pos C])] at h2
    nlinarith
  have hp := mul_neg_of_pos_of_neg (show 0<2*normalizedB C by positivity) C.property.2.1
  have hm := mul_neg_of_pos_of_neg (show 0<2*normalizedB C by positivity) C.property.2.2
  rw [hplus] at hp
  rw [hminus] at hm
  have hpa : 0<normalizedU C-normalizedA C := by linarith [le_abs_self (normalizedA C)]
  have hma : 0<normalizedU C+normalizedA C := by linarith [neg_abs_le (normalizedA C)]
  have hp' : normalizedB C<normalizedU C-normalizedA C :=
    (sq_lt_sq₀ hw.le hpa.le).mp (by linarith)
  have hm' : normalizedB C<normalizedU C+normalizedA C :=
    (sq_lt_sq₀ hw.le hma.le).mp (by linarith)
  rcases le_total 0 (normalizedA C) with h|h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

end polyak.Levels.Chart

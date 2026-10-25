import polyak.Levels.Program.Curve
import polyak.Levels.Chart.Coefficients
import polyak.General.AngleComparison

/-! Shifted tuning curves are actual closed-interval curves. A nonvanishing
polar normalization proves joint continuity, including both frequency ends,
without first assuming an interior arccotangent formula. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

def shiftNumerator (q : Tuning) (s ω : ℝ) : ℝ := q.Xi (Real.cos ω)+s*Real.sin ω

def shiftRadius (q : Tuning) (s ω : ℝ) : ℝ :=
  Real.sqrt ((shiftNumerator q s ω)^2+(Real.sin ω)^2)

def shiftedAngle (q : Tuning) (s ω : ℝ) : ℝ :=
  Real.arccos (shiftNumerator q s ω/shiftRadius q s ω)

theorem shiftRadius_pos (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    0<shiftRadius q s ω := by
  apply Real.sqrt_pos.mpr
  rcases eq_or_lt_of_le hω.1 with h|h
  · subst ω
    simp only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero,
      zero_pow (by norm_num : 2≠0)]
    exact sq_pos_of_neg q.Xi_one_neg
  · rcases eq_or_lt_of_le hω.2 with hp|hp
    · subst ω
      simp only [shiftNumerator,Real.cos_pi,Real.sin_pi,mul_zero,add_zero,
        zero_pow (by norm_num : 2≠0)]
      exact sq_pos_of_neg q.Xi_neg_one_neg
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi h hp))

theorem abs_shiftNumerator_le_radius (q : Tuning) (s ω : ℝ) :
    |shiftNumerator q s ω|≤shiftRadius q s ω := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (Real.sin ω),sq_abs (shiftNumerator q s ω)]

@[simp] theorem shiftedAngle_zero (q : Tuning) (s : ℝ) : shiftedAngle q s 0=Real.pi := by
  unfold shiftedAngle shiftRadius shiftNumerator
  simp only [Real.cos_zero,Real.sin_zero,mul_zero,add_zero,zero_pow (by norm_num : 2≠0),
    Real.sqrt_sq_eq_abs,abs_of_neg q.Xi_one_neg]
  rw [div_neg_eq_neg_div,div_self q.Xi_one_neg.ne,Real.arccos_neg_one]

@[simp] theorem shiftedAngle_pi (q : Tuning) (s : ℝ) : shiftedAngle q s Real.pi=Real.pi := by
  unfold shiftedAngle shiftRadius shiftNumerator
  simp only [Real.cos_pi,Real.sin_pi,mul_zero,add_zero,zero_pow (by norm_num : 2≠0),
    Real.sqrt_sq_eq_abs,abs_of_neg q.Xi_neg_one_neg]
  rw [div_neg_eq_neg_div,div_self q.Xi_neg_one_neg.ne,Real.arccos_neg_one]

theorem shiftedAngle_mem (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    shiftedAngle q s ω∈Ioo 0 Real.pi := by
  have hR:=shiftRadius_pos q s ⟨hω.1.le,hω.2.le⟩
  have hs:=Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hsq : (shiftRadius q s ω)^2=(shiftNumerator q s ω)^2+(Real.sin ω)^2 :=
    Real.sq_sqrt (by positivity)
  have hlt : |shiftNumerator q s ω|<shiftRadius q s ω := by
    nlinarith [sq_abs (shiftNumerator q s ω),abs_nonneg (shiftNumerator q s ω),sq_pos_of_pos hs]
  have hq:=abs_lt.mp hlt
  exact ⟨Real.arccos_pos.mpr ((div_lt_one hR).mpr hq.2),
    Real.arccos_lt_pi.mpr ((lt_div_iff₀ hR).mpr (by linarith))⟩

theorem shiftNumerator_jointContinuous :
    Continuous (fun p : Tuning×ℝ×Frequency=>shiftNumerator p.1 p.2.1 p.2.2) := by
  unfold shiftNumerator
  simp only [←Chart.eval_coefficients]
  unfold Chart.Coefficients.eval
  have hC : Continuous (fun p : Tuning×ℝ×Frequency=>Chart.coefficients p.1) :=
    Chart.continuous_coefficients.comp continuous_fst
  exact (((Chart.Coefficients.continuous_c0.comp hC).add
    ((Chart.Coefficients.continuous_c1.comp hC).mul
      (Real.continuous_cos.comp (continuous_subtype_val.comp continuous_snd.snd)))).add
    ((Chart.Coefficients.continuous_c2.comp hC).mul
      ((Real.continuous_cos.comp (continuous_subtype_val.comp continuous_snd.snd)).pow 2))).add
    (continuous_snd.fst.mul (Real.continuous_sin.comp (continuous_subtype_val.comp continuous_snd.snd)))

/-- Joint continuity in the genuine tuning topology, shift and closed
frequency interval, rather than only separate continuity in omega. -/
theorem shiftedAngle_jointContinuous :
    Continuous (fun p : Tuning×ℝ×Frequency=>shiftedAngle p.1 p.2.1 p.2.2) := by
  have hn := shiftNumerator_jointContinuous
  have hR : Continuous (fun p : Tuning×ℝ×Frequency=>shiftRadius p.1 p.2.1 p.2.2) := by
    unfold shiftRadius
    fun_prop
  exact Real.continuous_arccos.comp (hn.div hR (fun p=>(shiftRadius_pos p.1 p.2.1 p.2.2.property).ne'))

theorem continuous_shiftedAngle_frequency (q : Tuning) (s : ℝ) :
    Continuous (fun ω : Frequency=>shiftedAngle q s ω) := by
  have hx : Continuous q.Xi := by unfold Tuning.Xi; fun_prop
  have hn : Continuous (fun ω : Frequency=>shiftNumerator q s ω) :=
    (hx.comp (Real.continuous_cos.comp continuous_subtype_val)).add
      (continuous_const.mul (Real.continuous_sin.comp continuous_subtype_val))
  have hR : Continuous (fun ω : Frequency=>shiftRadius q s ω) :=
    Real.continuous_sqrt.comp ((hn.pow 2).add
      ((Real.continuous_sin.comp continuous_subtype_val).pow 2))
  exact Real.continuous_arccos.comp (hn.div hR (fun ω=>(shiftRadius_pos q s ω.property).ne'))

def shiftedCurve (q : Tuning) (s : ℝ) : Curve where
  toFun:=fun ω=>shiftedAngle q s ω
  continuous_toFun:=continuous_shiftedAngle_frequency q s
  pos ω:=by
    rcases eq_or_lt_of_le ω.property.1 with h|h
    · simpa only [←h,shiftedAngle_zero] using Real.pi_pos
    rcases eq_or_lt_of_le ω.property.2 with hp|hp
    · simpa only [hp,shiftedAngle_pi] using Real.pi_pos
    exact (shiftedAngle_mem q s ⟨h,hp⟩).1
  le_pi _:=Real.arccos_le_pi _
  at_zero:=shiftedAngle_zero q s
  at_pi:=shiftedAngle_pi q s

@[simp] theorem shiftedCurve_apply (q : Tuning) (s : ℝ) (ω : Frequency) :
    shiftedCurve q s ω=shiftedAngle q s ω := rfl

@[simp] theorem shiftedCurve_zero (q : Tuning) : shiftedCurve q 0=tuningCurve q := by
  apply Curve.ext
  intro ω
  simp only [shiftedCurve_apply,tuningCurve_apply,shiftedAngle,shiftRadius,shiftNumerator,
    zero_mul,add_zero,Tuning.angle,Tuning.angleRadius]

theorem cos_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    Real.cos (shiftedAngle q s ω)=shiftNumerator q s ω/shiftRadius q s ω := by
  apply Real.cos_arccos
  · exact (le_div_iff₀ (shiftRadius_pos q s hω)).mpr
      (by linarith [(abs_le.mp (abs_shiftNumerator_le_radius q s ω)).1])
  · exact (div_le_one (shiftRadius_pos q s hω)).mpr
      ((le_abs_self _).trans (abs_shiftNumerator_le_radius q s ω))

theorem sin_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    Real.sin (shiftedAngle q s ω)=Real.sin ω/shiftRadius q s ω := by
  have hR:=shiftRadius_pos q s hω
  have hs:=Real.sin_nonneg_of_nonneg_of_le_pi hω.1 hω.2
  have hangle : 0≤Real.sin (shiftedAngle q s ω) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)
  have hh:=Real.sin_sq_add_cos_sq (shiftedAngle q s ω)
  rw [cos_shiftedAngle q s hω] at hh
  have hsq : (shiftRadius q s ω)^2=(shiftNumerator q s ω)^2+(Real.sin ω)^2 :=
    Real.sq_sqrt (by positivity)
  have he : (Real.sin (shiftedAngle q s ω))^2=(Real.sin ω/shiftRadius q s ω)^2 := by
    field_simp at hh ⊢
    nlinarith
  nlinarith [div_nonneg hs hR.le]

theorem cot_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    Real.cos (shiftedAngle q s ω)/Real.sin (shiftedAngle q s ω)=
      q.Xi (Real.cos ω)/Real.sin ω+s := by
  rw [cos_shiftedAngle q s ⟨hω.1.le,hω.2.le⟩,sin_shiftedAngle q s ⟨hω.1.le,hω.2.le⟩]
  unfold shiftNumerator
  field_simp [(shiftRadius_pos q s ⟨hω.1.le,hω.2.le⟩).ne',
    (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne']

end polyak.Levels.Geometry

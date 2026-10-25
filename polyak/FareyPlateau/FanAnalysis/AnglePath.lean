import polyak.FareyPlateau.FanAnalysis.JetCalculus
import polyak.FareyPlateau.Edge.Adjacent

/-! The genuine phase on the two shrinking fan frequencies and the
quadratically shifted tuning. Its second jet includes the shift contribution. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels Filter Set
open scoped Topology

def cotPath (q : Tuning) (s ω h e δ : ℝ) : ℝ :=
  Geometry.cotangent q (ω + h * δ) + s - e * δ^2

def anglePath (q : Tuning) (s ω h e δ : ℝ) : ℝ :=
  Geometry.arccotangent (cotPath q s ω h e δ)

theorem analyticAt_cotangent (q : Tuning) {ω : ℝ} (hω : ω ∈ Ioo 0 Real.pi) :
    AnalyticAt ℝ (Geometry.cotangent q) ω := by
  rw [Geometry.cotangent_eq_poly]
  unfold Geometry.polyCotangent
  apply AnalyticAt.div _ Real.analyticAt_sin (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'
  fun_prop

theorem analyticAt_cotPath (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    AnalyticAt ℝ (cotPath q s ω h e) 0 := by
  have ha : AnalyticAt ℝ (fun δ : ℝ => ω + h * δ) 0 := by fun_prop
  have hp := (analyticAt_cotangent q (show ω + h * 0 ∈ Ioo 0 Real.pi by simpa only [mul_zero, add_zero] using hω)).comp (f := fun δ : ℝ => ω + h * δ) ha
  unfold cotPath
  exact (hp.add analyticAt_const).sub (analyticAt_const.mul (analyticAt_id.pow 2))

theorem analyticAt_anglePath (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    AnalyticAt ℝ (anglePath q s ω h e) 0 := by
  have hp := analyticAt_cotPath q s ω h e hω
  exact analyticAt_const.sub ((analyticAt_real_arctan _).comp hp)

theorem anglePath_actual (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    anglePath q s ω h e =ᶠ[𝓝 0]
      fun δ => Geometry.shiftedAngle q (s - e * δ^2) (ω + h * δ) := by
  have ha : ContinuousAt (fun δ : ℝ => ω + h * δ) 0 := by fun_prop
  have he := ha.eventually (isOpen_Ioo.mem_nhds (show ω + h * 0 ∈ Ioo 0 Real.pi by simpa only [mul_zero, add_zero] using hω))
  filter_upwards [he] with δ hδ
  rw [Geometry.shiftedAngle_eq_arccotangent q _ hδ]
  unfold anglePath cotPath
  congr 1
  ring

theorem cotPath_first (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    deriv (cotPath q s ω h e) 0 = Geometry.cotangentFirst q ω * h := by
  have ha : HasDerivAt (fun δ : ℝ => ω + h * δ) h 0 := by
    simpa only [mul_zero, add_zero, id_eq, mul_one] using (((hasDerivAt_id (0 : ℝ)).const_mul h).const_add ω)
  have hp := ((Geometry.hasDerivAt_cotangent q (show ω + h * 0 ∈ Ioo 0 Real.pi by simpa only [mul_zero, add_zero] using hω)).comp 0 ha).add_const s
  have hδ := (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul e)
  have hh := hp.sub hδ
  change deriv (fun δ => Geometry.cotangent q (ω + h * δ) + s - e * δ^2) 0 = _
  convert hh.deriv using 1 <;> simp [Pi.sub_def]

theorem cotPath_second (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    deriv^[2] (cotPath q s ω h e) 0 = Geometry.cotangentSecond q ω * h^2 - 2 * e := by
  have he : deriv (cotPath q s ω h e) =ᶠ[𝓝 0]
      fun δ => Geometry.cotangentFirst q (ω + h * δ) * h - 2 * e * δ := by
    have ha : ContinuousAt (fun δ : ℝ => ω + h * δ) 0 := by fun_prop
    filter_upwards [ha.eventually (isOpen_Ioo.mem_nhds (show ω + h * 0 ∈ Ioo 0 Real.pi by simpa only [mul_zero, add_zero] using hω))] with δ hδ
    have hd : HasDerivAt (fun δ : ℝ => ω + h * δ) h δ := by
      simpa only [id_eq, mul_one] using (((hasDerivAt_id δ).const_mul h).const_add ω)
    have hc := (((Geometry.hasDerivAt_cotangent q hδ).comp δ hd).add_const s).sub
      (((hasDerivAt_id δ).pow 2).const_mul e)
    convert hc.deriv using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have ha : HasDerivAt (fun δ : ℝ => ω + h * δ) h 0 := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id (0 : ℝ)).const_mul h).const_add ω)
  have hd := (((Geometry.hasDerivAt_cotangentFirst q (show ω + h * 0 ∈ Ioo 0 Real.pi by simpa only [mul_zero, add_zero] using hω)).comp 0 ha).mul_const h).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul (2 * e))
  change deriv (deriv (cotPath q s ω h e)) 0 = _
  rw [he.deriv_eq]
  convert hd.deriv using 1 <;> first | rfl | (simp only [mul_zero, add_zero]; ring)

theorem arccot_second {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    deriv^[2] (fun y => Geometry.arccotangent (f y)) x =
      -deriv^[2] f x / (1 + (f x)^2) +
        2 * f x * (deriv f x)^2 / (1 + (f x)^2)^2 := by
  have he : deriv (fun y => Geometry.arccotangent (f y)) =ᶠ[𝓝 x]
      fun y => -deriv f y / (1 + (f y)^2) := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    have hd := (Geometry.hasDerivAt_arccotangent (f y)).comp y hy.differentiableAt.hasDerivAt
    convert hd.deriv using 1 <;> first | rfl | ring
  have hn : 1 + (f x)^2 ≠ 0 := by positivity
  have hden := ((hf.differentiableAt.hasDerivAt.pow 2).const_add 1)
  have hd := hf.deriv.differentiableAt.hasDerivAt.neg.div hden hn
  change deriv (deriv (fun y => Geometry.arccotangent (f y))) x = _
  rw [he.deriv_eq]
  convert hd.deriv using 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Pi.pow_apply, Pi.neg_apply, Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp [hn]
  ring

theorem anglePath_value (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    anglePath q s ω h e 0 = Geometry.shiftedAngle q s ω := by
  rw [Geometry.shiftedAngle_eq_arccotangent q s hω]
  simp only [anglePath, cotPath, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero]

theorem anglePath_first (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    deriv (anglePath q s ω h e) 0 = Geometry.shiftedFirst q s ω * h := by
  have hd := (Geometry.hasDerivAt_arccotangent (cotPath q s ω h e 0)).comp 0
    (analyticAt_cotPath q s ω h e hω).differentiableAt.hasDerivAt
  change deriv (fun δ => Geometry.arccotangent (cotPath q s ω h e δ)) 0 = _
  change deriv (Geometry.arccotangent ∘ cotPath q s ω h e) 0 = _
  rw [hd.deriv, cotPath_first q s ω h e hω]
  simp only [cotPath, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Geometry.shiftedFirst]
  ring

theorem anglePath_second (q : Tuning) (s ω h e : ℝ) (hω : ω ∈ Ioo 0 Real.pi) :
    deriv^[2] (anglePath q s ω h e) 0 = Geometry.shiftedSecond q s ω * h^2 +
      2 * e / (1 + (Geometry.cotangent q ω + s)^2) := by
  unfold anglePath
  rw [arccot_second (analyticAt_cotPath q s ω h e hω), cotPath_second q s ω h e hω,
    cotPath_first q s ω h e hω]
  simp only [cotPath, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero, Geometry.shiftedSecond]
  ring

end polyak.FareyPlateau.FanAnalysis

import polyak.Levels.Geometry.LagFactor

/-! Removing the quadratic endpoint zero produces continuous functions on
exactly the original compact frequency interval. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

def normalizedLag (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency) : ℝ :=
  if ω=frequencyZero then -(n:ℝ)*((n:ℝ)+2*tau q)/2
  else (shiftedCurve q s).lag n ω/(ω:ℝ)^2

@[simp] theorem normalizedLag_zero (q : Tuning) (s : ℝ) (n : ℤ) :
    normalizedLag q s n frequencyZero= -(n:ℝ)*((n:ℝ)+2*tau q)/2 := by
  simp only [normalizedLag,ite_true]

theorem lag_eq_sq_mul_normalizedLag (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency) :
    (shiftedCurve q s).lag n ω=(ω:ℝ)^2*normalizedLag q s n ω := by
  by_cases he : ω=frequencyZero
  · subst ω
    rw [Curve.lag_at_zero]
    change 0=(0:ℝ)^2*normalizedLag q s n frequencyZero
    ring
  · have hn : (ω:ℝ)≠0:=fun hh=>he (Subtype.ext hh)
    simp only [normalizedLag,ite_eq_right he]
    field_simp

theorem endLag_eventually_eq_lag (q : Tuning) (s : ℝ) (n : ℤ) :
    ∀ᶠω : Frequency in 𝓝 frequencyZero,
      endLag q s n ω=(shiftedCurve q s).lag n ω := by
  have hn : shiftNumerator q s frequencyZero<0 := by
    simpa only [frequencyZero,shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg
  have hc:=((analyticAt_shiftNumerator q s 0).continuousAt).comp
    (x:=frequencyZero) continuous_subtype_val.continuousAt
  filter_upwards [hc.eventually (eventually_lt_nhds hn)] with ω hω
  simp only [endLag,extendedLag,endAngle_eq_shiftedAngle q s ω.property hω,Curve.lag,shiftedCurve_apply]

theorem continuous_normalizedLag (q : Tuning) (s : ℝ) (n : ℤ) :
    Continuous (normalizedLag q s n) := by
  rw [continuous_iff_continuousAt]
  intro ω
  by_cases he : ω=frequencyZero
  · subst ω
    obtain ⟨U,hU,hU0,hfactor⟩:=endLag_quadratic_factor q s n
    have hc : ContinuousAt (fun ω : Frequency=>U (ω:ℝ)) frequencyZero :=
      ContinuousAt.comp (f:=fun ω : Frequency=>(ω:ℝ)) (x:=frequencyZero) hU.continuousAt continuous_subtype_val.continuousAt
    apply hc.congr
    have hfact : ∀ᶠω : Frequency in 𝓝 frequencyZero,
        normalizedLag q s n ω=U (ω:ℝ) := by
      filter_upwards [endLag_eventually_eq_lag q s n] with ω hω
      by_cases hz : ω=frequencyZero
      · subst ω
        rw [normalizedLag_zero]
        exact hU0.symm
      · have hn : (ω:ℝ)≠0:=fun hh=>hz (Subtype.ext hh)
        rw [normalizedLag,ite_eq_right hz,←hω,hfactor]
        exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hn)
    filter_upwards [hfact] with ω hω
    exact hω.symm
  · have hv : (ω:ℝ)≠0:=fun hh=>he (Subtype.ext hh)
    have hc:=((shiftedCurve q s).continuous_lag n).continuousAt.div
      (continuous_subtype_val.continuousAt.pow 2) (pow_ne_zero 2 hv)
    apply hc.congr
    filter_upwards [eventually_ne_nhds he] with x hx
    simp only [normalizedLag,ite_eq_right hx]
    rfl

end polyak.Levels.Geometry

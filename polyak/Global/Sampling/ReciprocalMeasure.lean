import polyak.Global.Sampling.MonoformStrictness
import polyak.Levels.Threshold.Monoform

/-! The actual reciprocal-sine measure, including exact strict-moment
transfer. This is an arbitrary finite measure, not an atomic replacement. -/
noncomputable section
namespace polyak.Global.Sampling
open Levels Levels.Threshold MeasureTheory Set Filter

 theorem measure_of_monotone_solution (q : General.Tuning) (s : ℝ)
    {ν : Measure Frequency} (hν : MonotoneSolution (shiftedCotangent q s) ν) :
    ∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w ∧
      (∀ᵐω∂w,ω∈interiorCarrier) ∧
      ((∫ω,(Geometry.shiftedCurve q s).minimizer ω∂w)=∫ω,shiftedCotangent q s ω∂ν) ∧
      ∀n : ℤ,(∫ω,(Geometry.shiftedCurve q s).lag n ω∂w)=
        ∫ω,monotoneLag (shiftedCotangent q s) n ω∂ν := by
  let Θ := Geometry.shiftedCurve q s
  let h := shiftedCotangent q s
  let d : Frequency→ℝ := fun ω=>1/Real.sin (Θ ω)
  have : IsFiniteMeasure ν := hν.1
  have hcar := hν.2.2.1
  have hh := hν.2.2.2.1
  have hspos (ω : Frequency) (hω : ω∈interiorCarrier) : 0<Real.sin (Θ ω) := by
    exact Real.sin_pos_of_pos_of_lt_pi (Θ.pos ω) (Geometry.shiftedAngle_mem q s hω).2
  have hcot (ω : Frequency) (hω : ω∈interiorCarrier) : Real.cos (Θ ω)=Real.sin (Θ ω)*h ω := by
    have he := Geometry.cot_shiftedAngle q s hω
    simpa only [Θ,Geometry.shiftedCurve_apply,h,shiftedCotangent,Geometry.cotangent,mul_comm] using
      (div_eq_iff (hspos ω hω).ne').mp he
  have hlag (n : ℤ) (ω : Frequency) (hω : ω∈interiorCarrier) :
      Θ.lag n ω=Real.sin (Θ ω)*monotoneLag h n ω := by
    rw [Θ.lag_expand,hcot ω hω]
    unfold monotoneLag
    ring
  have hdm : Measurable d := measurable_const.div (Real.continuous_sin.comp Θ.continuous).measurable
  have hdnonneg (ω : Frequency) : 0≤d ω := one_div_nonneg.mpr (phase_sine_nonneg Θ ω)
  have hdpos : ∀ᵐω∂ν,0<d ω := hcar.mono (fun ω hω=>one_div_pos.mpr (hspos ω hω))
  have hbound (ω : Frequency) (hω : ω∈interiorCarrier) : d ω≤1+|h ω| := by
    have hs := hspos ω hω
    have hc := hcot ω hω
    have hid := Real.sin_sq_add_cos_sq (Θ ω)
    rw [hc] at hid
    have he : (d ω)^2=1+(h ω)^2 := by
      dsimp [d]
      field_simp
      nlinarith [sq_nonneg (Real.sin (Θ ω)*h ω)]
    nlinarith [abs_nonneg (h ω),sq_abs (h ω),hdnonneg ω]
  have hdi : Integrable d ν :=
    ((integrable_const (1:ℝ)).add hh.abs).mono' hdm.aestronglyMeasurable
      (hcar.mono fun ω hω=>by rw [Real.norm_eq_abs,abs_of_nonneg (hdnonneg ω)];exact hbound ω hω)
  let w := realWeight d ν
  have hwfinite : IsFiniteMeasure w := isFiniteMeasure_withDensity_ofReal hdi.2
  have hwne : w≠0 := realWeight_ne_zero hdm hdpos hν.2.1
  have hcancel (ω : Frequency) (hω : ω∈interiorCarrier) : d ω*Real.sin (Θ ω)=1 :=
    one_div_mul_cancel (hspos ω hω).ne'
  have hg : (∫ω,Θ.minimizer ω∂w)=∫ω,h ω∂ν := by
    rw [integral_realWeight hdm hdnonneg]
    apply integral_congr_ae
    filter_upwards [hcar] with ω hω
    change d ω*Real.cos (Θ ω)=h ω
    rw [hcot ω hω,←mul_assoc,hcancel ω hω,one_mul]
  have hl (n : ℤ) : (∫ω,Θ.lag n ω∂w)=∫ω,monotoneLag h n ω∂ν := by
    rw [integral_realWeight hdm hdnonneg]
    apply integral_congr_ae
    filter_upwards [hcar] with ω hω
    rw [hlag n ω hω,←mul_assoc,hcancel ω hω,one_mul]
  refine ⟨w,⟨hwfinite,hwne,?_,fun n hn=>?_⟩,(realWeight_ac d ν).ae_le hcar,hg,hl⟩
  · rw [hg]
    exact hν.2.2.2.2.1
  · rw [hl]
    exact hν.2.2.2.2.2 n hn

 theorem strict_measure_of_monotone (q : General.Tuning) (s : ℝ)
    {ν : Measure Frequency} (hν : MonotoneSolution (shiftedCotangent q s) ν)
    (hmin : 0<∫ω,shiftedCotangent q s ω∂ν)
    (hlag : ∀n : ℤ,n≠0→0<∫ω,monotoneLag (shiftedCotangent q s) n ω∂ν) :
    ∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w ∧
      (∀ᵐω∂w,ω∈interiorCarrier) ∧
      (0<∫ω,(Geometry.shiftedCurve q s).minimizer ω∂w) ∧
      ∀n : ℤ,n≠0→0<∫ω,(Geometry.shiftedCurve q s).lag n ω∂w := by
  obtain ⟨w,hw,hcar,hm,hl⟩ := measure_of_monotone_solution q s hν
  exact ⟨w,hw,hcar,by rw [hm];exact hmin,fun n hn=>by rw [hl];exact hlag n hn⟩

end polyak.Global.Sampling

import polyak.Levels.Threshold.MeasureTools
import polyak.Levels.Program.EndpointRemoval
import polyak.Levels.Geometry.Arccotangent

/-! The integrable monotone formulation of the full program. Measures are
carried by the open frequency interval; no finite-support restriction is made. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

def monotoneLag (h : Frequency→ℝ) (n : ℤ) (ω : Frequency) : ℝ :=
  h ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))-Real.sin ((n:ℝ)*(ω:ℝ))

def MonotoneSolution (h : Frequency→ℝ) (ν : Measure Frequency) : Prop :=
  IsFiniteMeasure ν ∧ ν≠0 ∧ (∀ᵐω∂ν,ω∈interiorCarrier) ∧ Integrable h ν ∧
    0≤∫ ω,h ω ∂ν ∧ ∀n:ℤ,n≠0→0≤∫ ω,monotoneLag h n ω ∂ν

theorem phase_sine_nonneg (Θ : Curve) (ω : Frequency) : 0≤Real.sin (Θ ω) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (Θ.pos ω).le (Θ.le_pi ω)

theorem curve_monoform_carried_iff (Θ : Curve) (h : Frequency→ℝ) (_hm : Measurable h)
    (hstrict : ∀ω∈interiorCarrier,Θ ω<Real.pi)
    (hcot : ∀ω∈interiorCarrier,Real.cos (Θ ω)=Real.sin (Θ ω)*h ω) (A : Set Frequency) :
    (∃w : Measure Frequency,ProgramSolution Θ nonzeroLags w ∧ (∀ᵐω∂w,ω∈A)) ↔
      ∃ν : Measure Frequency,MonotoneSolution h ν ∧ (∀ᵐω∂ν,ω∈A) := by
  have hspos (ω:Frequency) (hω:ω∈interiorCarrier) : 0<Real.sin (Θ ω) :=
    Real.sin_pos_of_pos_of_lt_pi (Θ.pos ω) (hstrict ω hω)
  have hlag (n:ℤ) (ω:Frequency) (hω:ω∈interiorCarrier) :
      Θ.lag n ω=Real.sin (Θ ω)*monotoneLag h n ω := by
    rw [Θ.lag_expand,hcot ω hω]
    dsimp [monotoneLag]
    ring
  constructor
  · rintro ⟨w,hw,hA⟩
    let u := w.restrict interiorCarrier
    have hu : ProgramSolution Θ nonzeroLags u := by
      simpa only [u,interiorCarrier] using hw.remove_endpoints
    have : IsFiniteMeasure u := hu.1
    have hucar : ∀ᵐω∂u,ω∈interiorCarrier := ae_restrict_mem measurableSet_interiorCarrier
    let d : C(Frequency,ℝ) := ⟨fun ω => Real.sin (Θ ω),Real.continuous_sin.comp Θ.continuous⟩
    let ν := realWeight d u
    have hνfinite : IsFiniteMeasure ν := by change IsFiniteMeasure (reweight d u); infer_instance
    have hνne : ν≠0 := realWeight_ne_zero d.continuous.measurable
      (hucar.mono fun ω hω => hspos ω hω) hu.2.1
    have hνcar : ∀ᵐω∂ν,ω∈interiorCarrier := (realWeight_ac d u).ae_le hucar
    have hAu : ∀ᵐω∂u,ω∈A := ae_mono Measure.restrict_le_self hA
    have hAν : ∀ᵐω∂ν,ω∈A := (realWeight_ac d u).ae_le hAu
    have hhi : Integrable h ν := by
      apply (integrable_realWeight_iff d.continuous.measurable (phase_sine_nonneg Θ) u h).mpr
      exact (integrable_curve_minimizer Θ u).congr (hucar.mono fun ω hω => hcot ω hω)
    have hg : (∫ ω,h ω ∂ν)=∫ ω,Θ.minimizer ω ∂u := by
      rw [integral_realWeight d.continuous.measurable (phase_sine_nonneg Θ)]
      exact integral_congr_ae (hucar.mono fun ω hω => (hcot ω hω).symm)
    have hl (n:ℤ) : (∫ ω,monotoneLag h n ω ∂ν)=∫ ω,Θ.lag n ω ∂u := by
      rw [integral_realWeight d.continuous.measurable (phase_sine_nonneg Θ)]
      exact integral_congr_ae (hucar.mono fun ω hω => (hlag n ω hω).symm)
    refine ⟨ν,⟨hνfinite,hνne,hνcar,hhi,?_,fun n hn => ?_⟩,hAν⟩
    · rw [hg]
      exact hu.2.2.1
    · rw [hl]
      exact hu.2.2.2 n hn
  · rintro ⟨ν,⟨hfinite,hne,hcar,hhi,hG,hL⟩,hA⟩
    have : IsFiniteMeasure ν := hfinite
    let d : Frequency→ℝ := fun ω => 1/Real.sin (Θ ω)
    have hdm : Measurable d := measurable_const.div (Real.continuous_sin.comp Θ.continuous).measurable
    have hdnonneg (ω:Frequency) : 0≤d ω := one_div_nonneg.mpr (phase_sine_nonneg Θ ω)
    have hdpos : ∀ᵐω∂ν,0<d ω := hcar.mono fun ω hω => one_div_pos.mpr (hspos ω hω)
    have hbound (ω:Frequency) (hω:ω∈interiorCarrier) : d ω≤1+|h ω| := by
      have hs:=hspos ω hω
      have hc:=hcot ω hω
      have hid := Real.sin_sq_add_cos_sq (Θ ω)
      rw [hc] at hid
      have he : (d ω)^2=1+(h ω)^2 := by
        dsimp [d]
        field_simp
        nlinarith [sq_nonneg (Real.sin (Θ ω)*h ω)]
      nlinarith [abs_nonneg (h ω),sq_abs (h ω),hdnonneg ω]
    have hdi : Integrable d ν :=
      ((integrable_const (1:ℝ)).add hhi.abs).mono' hdm.aestronglyMeasurable
        (hcar.mono fun ω hω => by rw [Real.norm_eq_abs,abs_of_nonneg (hdnonneg ω)]; exact hbound ω hω)
    let w := realWeight d ν
    have hwfinite : IsFiniteMeasure w := isFiniteMeasure_withDensity_ofReal hdi.2
    have hwne : w≠0 := realWeight_ne_zero hdm hdpos hne
    have hcancel (ω:Frequency) (hω:ω∈interiorCarrier) : d ω*Real.sin (Θ ω)=1 := by
      exact one_div_mul_cancel (hspos ω hω).ne'
    have hg : (∫ ω,Θ.minimizer ω ∂w)=∫ ω,h ω ∂ν := by
      rw [integral_realWeight hdm hdnonneg]
      apply integral_congr_ae
      filter_upwards [hcar] with ω hω
      change d ω*Real.cos (Θ ω)=h ω
      rw [hcot ω hω,← mul_assoc,hcancel ω hω,one_mul]
    have hl (n:ℤ) : (∫ ω,Θ.lag n ω ∂w)=∫ ω,monotoneLag h n ω ∂ν := by
      rw [integral_realWeight hdm hdnonneg]
      apply integral_congr_ae
      filter_upwards [hcar] with ω hω
      rw [hlag n ω hω,← mul_assoc,hcancel ω hω,one_mul]
    refine ⟨w,⟨hwfinite,hwne,?_,fun n hn => ?_⟩,(realWeight_ac d ν).ae_le hA⟩
    · rw [hg]
      exact hG
    · rw [hl]
      exact hL n hn

theorem curve_monoform_iff (Θ : Curve) (h : Frequency→ℝ) (hm : Measurable h)
    (hstrict : ∀ω∈interiorCarrier,Θ ω<Real.pi)
    (hcot : ∀ω∈interiorCarrier,Real.cos (Θ ω)=Real.sin (Θ ω)*h ω) :
    FP Θ ↔ ∃ν : Measure Frequency,MonotoneSolution h ν := by
  simpa only [FP,FPOn,Set.mem_univ,Filter.eventually_true,and_true] using
    curve_monoform_carried_iff Θ h hm hstrict hcot Set.univ

def shiftedCotangent (q : General.Tuning) (s : ℝ) (ω : Frequency) : ℝ :=
  Geometry.cotangent q ω+s

theorem shifted_monoform_iff (q : General.Tuning) (s : ℝ) :
    FP (Geometry.shiftedCurve q s) ↔ ∃ν : Measure Frequency,MonotoneSolution (shiftedCotangent q s) ν := by
  apply curve_monoform_iff
  · unfold shiftedCotangent Geometry.cotangent General.Tuning.Xi
    fun_prop
  · intro ω hω
    exact (Geometry.shiftedAngle_mem q s hω).2
  · intro ω hω
    have he := Geometry.cot_shiftedAngle q s hω
    have hs := Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q s hω).1
      (Geometry.shiftedAngle_mem q s hω).2
    simpa only [Geometry.shiftedCurve_apply,shiftedCotangent,Geometry.cotangent,mul_comm] using
      (div_eq_iff hs.ne').mp he

theorem shifted_monoform_carried_iff (q : General.Tuning) (s : ℝ) (A : Set Frequency) :
    (∃w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w ∧ (∀ᵐω∂w,ω∈A)) ↔
      ∃ν : Measure Frequency,MonotoneSolution (shiftedCotangent q s) ν ∧ (∀ᵐω∂ν,ω∈A) := by
  apply curve_monoform_carried_iff
  · unfold shiftedCotangent Geometry.cotangent General.Tuning.Xi
    fun_prop
  · intro ω hω
    exact (Geometry.shiftedAngle_mem q s hω).2
  · intro ω hω
    have he := Geometry.cot_shiftedAngle q s hω
    have hs := Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q s hω).1
      (Geometry.shiftedAngle_mem q s hω).2
    simpa only [Geometry.shiftedCurve_apply,shiftedCotangent,Geometry.cotangent,mul_comm] using
      (div_eq_iff hs.ne').mp he

end polyak.Levels.Threshold

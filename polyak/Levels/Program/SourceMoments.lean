import polyak.Levels.Program.Weighting
import polyak.Waves.Interpolation
import polyak.Waves.Dynamics

/-! The source spectral slacks equal the weighted curve constraints, including endpoints. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

def angleMultiplier (q : General.Tuning) : C(Frequency,ℂ) :=
  (Waves.multiplierMap q.A q.B q.beta 0).comp
    ⟨Spectral.cosineCoordinates,Spectral.cosineCoordinates.continuous⟩

@[simp] theorem angleMultiplier_eq (q : General.Tuning) (ω : Frequency) :
    angleMultiplier q ω=q.m (Waves.z 0 ω) := by
  change Waves.multiplier q.A q.B q.beta 0 (Real.arccos (Real.cos (ω:ℝ)))=_
  rw [Real.arccos_cos ω.property.1 ω.property.2]
  rfl

def sourceDensity (q : General.Tuning) : C(Frequency,ℝ) where
  toFun ω := q.polarRadius ω
  continuous_toFun := by dsimp [General.Tuning.polarRadius,General.Tuning.angleRadius,General.Tuning.Xi]; fun_prop

theorem sourceDensity_pos (q : General.Tuning) (ω : Frequency) : 0<sourceDensity q ω :=
  q.polarRadius_pos ω.property

theorem sourceDensity_eq_norm (q : General.Tuning) (ω : Frequency) :
    sourceDensity q ω=‖(1-angleMultiplier q ω)*(1+star (angleMultiplier q ω))‖ := by
  have hp : 0<(2*(1-q.beta)/q.B)*q.angleRadius ω := q.polarRadius_pos ω.property
  rw [angleMultiplier_eq,q.threshold_polar ω.property,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hp,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.I_re,mul_zero,
    Complex.neg_im,Complex.ofReal_im,neg_zero,Complex.I_im,sub_self,
    Real.exp_zero,mul_one]
  rfl

def sourceG (q : General.Tuning) : C(Frequency,ℝ) :=
  ⟨fun ω => 1-Complex.normSq (angleMultiplier q ω),by fun_prop⟩

def sourceLag (q : General.Tuning) (n : ℤ) : C(Frequency,ℝ) :=
  ⟨fun ω => sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))-
    2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ)),by fun_prop⟩

theorem sourceG_polar (q : General.Tuning) (ω : Frequency) :
    sourceG q ω=sourceDensity q ω*(tuningCurve q).minimizer ω := by
  simpa only [sourceG,ContinuousMap.coe_mk,angleMultiplier_eq,sourceDensity,
    Curve.minimizer,tuningCurve_apply] using q.g_polar ω.property

theorem sourceLag_polar (q : General.Tuning) (n : ℤ) (ω : Frequency) :
    sourceLag q n ω=sourceDensity q ω*(tuningCurve q).lag n ω := by
  change sourceG q ω*(1-Real.cos ((n:ℝ)*(ω:ℝ)))-
    2*(angleMultiplier q ω).im*Real.sin ((n:ℝ)*(ω:ℝ))=_
  rw [sourceG_polar,(tuningCurve q).lag_expand,angleMultiplier_eq]
  have he := q.im_polar ω.property
  change 2*(q.m (Waves.z 0 ω)).im=sourceDensity q ω*Real.sin (tuningCurve q ω) at he
  rw [he]
  dsimp [Curve.minimizer]
  ring

def RawSpectrumSolution (q : General.Tuning) (μ : Measure Frequency) : Prop :=
  IsFiniteMeasure μ ∧ μ≠0 ∧ 0≤∫ ω,sourceG q ω ∂μ ∧
    ∀n:ℤ,n≠0→0≤∫ ω,sourceLag q n ω ∂μ

theorem rawSpectrumSolution_iff_reweight (q : General.Tuning) (μ : Measure Frequency) :
    RawSpectrumSolution q μ ↔ ProgramSolution (tuningCurve q) nonzeroLags (reweight (sourceDensity q) μ) := by
  have hg : (∫ ω,(tuningCurve q).minimizer ω ∂reweight (sourceDensity q) μ)=
      ∫ ω,sourceG q ω ∂μ := by
    rw [integral_reweight _ (fun ω => (sourceDensity_pos q ω).le)]
    congr 1
    funext ω
    exact (sourceG_polar q ω).symm
  have hl (n:ℤ) : (∫ ω,(tuningCurve q).lag n ω ∂reweight (sourceDensity q) μ)=
      ∫ ω,sourceLag q n ω ∂μ := by
    rw [integral_reweight _ (fun ω => (sourceDensity_pos q ω).le)]
    congr 1
    funext ω
    exact (sourceLag_polar q n ω).symm
  constructor
  · rintro ⟨hfinite,hne,hG,hL⟩
    have : IsFiniteMeasure μ := hfinite
    exact ⟨inferInstance,(reweight_ne_zero_iff _ (sourceDensity_pos q) μ).mpr hne,
      by simpa only [hg] using hG,fun n hn => by simpa only [hl n] using hL n hn⟩
  · rintro ⟨hfinite,hne,hG,hL⟩
    have : IsFiniteMeasure (reweight (sourceDensity q) μ) := hfinite
    have hback := reweight_reciprocal (sourceDensity q) (sourceDensity_pos q) μ
    have hfinite' : IsFiniteMeasure μ := by rw [← hback]; infer_instance
    exact ⟨hfinite',(reweight_ne_zero_iff _ (sourceDensity_pos q) μ).mp hne,
      by simpa only [hg] using hG,fun n hn => by simpa only [hl n] using hL n hn⟩

def thresholdMeasureEquiv (q : General.Tuning) :
    {μ : Measure Frequency // RawSpectrumSolution q μ} ≃
      {w : Measure Frequency // ProgramSolution (tuningCurve q) nonzeroLags w} where
  toFun μ := ⟨reweight (sourceDensity q) μ,(rawSpectrumSolution_iff_reweight q μ).mp μ.property⟩
  invFun w := ⟨reweight (reciprocalDensity (sourceDensity q) (sourceDensity_pos q)) w,by
    apply (rawSpectrumSolution_iff_reweight q _).mpr
    rw [reciprocal_reweight]
    exact w.property⟩
  left_inv μ := Subtype.ext (reweight_reciprocal _ _ μ)
  right_inv w := Subtype.ext (reciprocal_reweight _ _ w)

theorem RawSpectrumSolution.normalize {q : General.Tuning} {μ : Measure Frequency}
    (h : RawSpectrumSolution q μ) :
    ∃ν : ProbabilityMeasure Frequency, RawSpectrumSolution q ν := by
  let mf : FiniteMeasure Frequency := ⟨μ,h.1⟩
  have hm : mf≠0 := by intro he; exact h.2.1 (congrArg FiniteMeasure.toMeasure he)
  refine ⟨mf.normalize,inferInstance,IsProbabilityMeasure.ne_zero _,?_,?_⟩
  · rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) h.2.2.1
  · intro n hn
    rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) (h.2.2.2 n hn)

end polyak.Levels

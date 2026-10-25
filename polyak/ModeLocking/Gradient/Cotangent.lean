import polyak.ModeLocking.Continuation.Kernels
import polyak.Levels.Threshold.KappaDerivative

/-! The source cotangent in the three original parameters, with its genuine
ambient differential and strictly positive kappa derivative. -/
noncomputable section
namespace polyak.ModeLocking.Gradient
open General Levels Continuation

def sourceCotangent (ω:Frequency) (p:Parameters) : ℝ :=
  Geometry.ambientNumerator (Chart.rawToCoefficient ![p 0,p 1,p 2,0,(ω:ℝ)]) / Real.sin (ω:ℝ)

theorem sourceCotangent_actual (q:Tuning) (ω:Frequency) :
    sourceCotangent ω (parameters q)=Geometry.cotangent q ω := by
  unfold sourceCotangent
  change Geometry.ambientNumerator (Geometry.coefficientPoint q 0 ω)/Real.sin (ω:ℝ)=_
  rw [Geometry.ambientNumerator_coefficientPoint]
  simp only [Geometry.shiftNumerator,zero_mul,add_zero,Geometry.cotangent]

theorem analyticAt_sourceCotangent (q:Tuning) (ω:Frequency) :
    AnalyticAt ℝ (sourceCotangent ω) (parameters q) := by
  have hin : AnalyticAt ℝ (fun p:Parameters=>![p 0,p 1,p 2,0,(ω:ℝ)]) (parameters q) := by
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact (ContinuousLinearMap.proj (R:=ℝ) 0 : Parameters→L[ℝ]ℝ).analyticAt _
    · exact (ContinuousLinearMap.proj (R:=ℝ) 1 : Parameters→L[ℝ]ℝ).analyticAt _
    · exact (ContinuousLinearMap.proj (R:=ℝ) 2 : Parameters→L[ℝ]ℝ).analyticAt _
    · exact analyticAt_const
    · exact analyticAt_const
  have hout := (Geometry.analyticAt_ambientNumerator
    (Chart.rawToCoefficient ![q.kappa,q.y,q.beta,0,(ω:ℝ)])).comp
      (Chart.analyticAt_rawToCoefficient_actual q 0 ω)
  exact (hout.comp (f:=fun p:Parameters=>![p 0,p 1,p 2,0,(ω:ℝ)]) hin).div_const

theorem ambientPhase_interior (ω:Frequency)
    (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) (p:SourcePoint) :
    ambientPhase ω p=Real.pi/2-Real.arctan (sourceCotangent ω ![p 0,p 1,p 2]+p 3) := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  unfold ambientPhase Geometry.jointAngle Geometry.ambientAngle
  change (if 0<Real.sin (ω:ℝ) then _ else _)=_
  rw [ite_eq_left hs]
  unfold Geometry.ambientInteriorAngle Geometry.arccotangent sourceCotangent
  congr 1
  dsimp [Geometry.ambientNumerator,Chart.rawToCoefficient,Chart.rawA,Chart.rawB]
  field_simp
  ring

theorem sourceCotangent_kappa (q:Tuning) (ω:Frequency) (κ:ℝ) :
    sourceCotangent ω ![κ,q.y,q.beta]=XiAtKappa q κ (Real.cos (ω:ℝ))/Real.sin (ω:ℝ) := by
  unfold sourceCotangent Geometry.ambientNumerator Chart.rawToCoefficient Chart.rawA Chart.rawB XiAtKappa
  dsimp
  ring

theorem hasDerivAt_sourceCotangent_kappa (q:Tuning) (ω:Frequency) :
    HasDerivAt (fun κ=>sourceCotangent ω ![κ,q.y,q.beta])
      (kappaNumerator q.y q.beta (Real.cos (ω:ℝ)) /
        (q.y*(1-q.beta)*(q.kappa-1)^2*Real.sin (ω:ℝ))) q.kappa := by
  have hd:=(hasDerivAt_XiAtKappa q q.kappa_gt_one (Real.cos (ω:ℝ))).div_const (Real.sin (ω:ℝ))
  simp only [←sourceCotangent_kappa] at hd
  simpa only [div_div] using hd

end polyak.ModeLocking.Gradient

import polyak.ModeLocking.Gradient.Cotangent

/-! At a fixed interior atom, every lag depends on the source parameters
through h_q(omega)+s alone. -/
noncomputable section
namespace polyak.ModeLocking.Gradient
open General Levels Continuation

def continuedPoint (σ:Parameters→ℝ) (p:Parameters) : SourcePoint :=
  ![p 0,p 1,p 2,σ p]

theorem ambientLag_eq_shifted (q:Tuning) (ω:Frequency)
    (hω:ω∈Threshold.interiorCarrier) (σ:Parameters→ℝ) (p:Parameters) (n:ℤ) :
    ambientLag n ω (continuedPoint σ p)=
      (Geometry.shiftedCurve q (sourceCotangent ω p+σ p-Geometry.cotangent q ω)).lag n ω := by
  have hphase : ambientPhase ω (continuedPoint σ p)=
      Geometry.shiftedCurve q (sourceCotangent ω p+σ p-Geometry.cotangent q ω) ω := by
    rw [ambientPhase_interior ω hω]
    change Real.pi/2-Real.arctan (sourceCotangent ω ![p 0,p 1,p 2]+σ p)=
      Geometry.shiftedAngle q (sourceCotangent ω p+σ p-Geometry.cotangent q ω) ω
    have hp : ![p 0,p 1,p 2]=p := by ext i; fin_cases i <;> rfl
    rw [hp,Geometry.shiftedAngle_eq_arccotangent q _ hω]
    unfold Geometry.arccotangent
    congr 2
    ring
  simp only [ambientLag,hphase,Curve.lag]

theorem hasFDerivAt_continuedLag (q:Tuning) (s:ℝ) (ω:Frequency)
    (hω:ω∈Threshold.interiorCarrier) (n:ℤ) {σ:Parameters→ℝ}
    {dσ:Parameters→L[ℝ]ℝ} (hσ:HasFDerivAt σ dσ (parameters q))
    (hbase:σ (parameters q)=s) :
    HasFDerivAt (fun p=>ambientLag n ω (continuedPoint σ p))
      (deriv (fun t=>(Geometry.shiftedCurve q t).lag n ω) s •
        (fderiv ℝ (sourceCotangent ω) (parameters q)+dσ)) (parameters q) := by
  have hh:=((analyticAt_sourceCotangent q ω).differentiableAt.hasFDerivAt.add hσ).sub_const
    (Geometry.cotangent q ω)
  have hval : sourceCotangent ω (parameters q)+σ (parameters q)-Geometry.cotangent q ω=s := by
    rw [sourceCotangent_actual,hbase]
    ring
  have hd : HasDerivAt (fun t=>(Geometry.shiftedCurve q t).lag n ω)
      (deriv (fun t=>(Geometry.shiftedCurve q t).lag n ω) s) s :=
    (hasDerivAt_lag_shift q s n ω hω).differentiableAt.hasDerivAt
  have hd' : HasFDerivAt (fun t=>(Geometry.shiftedCurve q t).lag n ω)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (fun t=>(Geometry.shiftedCurve q t).lag n ω) s))
      (sourceCotangent ω (parameters q)+σ (parameters q)-Geometry.cotangent q ω) := by
    rw [hval]
    exact hd.hasFDerivAt
  have hc:=hd'.comp (parameters q) hh
  have he : (fun p=>ambientLag n ω (continuedPoint σ p))=
      (fun p=>(Geometry.shiftedCurve q
        (sourceCotangent ω p+σ p-Geometry.cotangent q ω)).lag n ω) :=
    funext (fun p=>ambientLag_eq_shifted q ω hω σ p n)
  rw [he]
  convert hc using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,smul_apply,
      add_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
    ring

end polyak.ModeLocking.Gradient

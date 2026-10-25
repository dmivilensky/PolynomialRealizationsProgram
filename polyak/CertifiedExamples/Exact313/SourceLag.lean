import polyak.CertifiedExamples.Exact313.Source

/-! Denominator-free residue and determinant reserves are exactly the source
lag and phase numerators; their omitted radii are proved strictly positive. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag

def rawLag (q : Tuning) (n : ℤ) (x : ℝ) : ℝ :=
  q.Xi (Real.cos x)*(1-Real.cos ((n:ℝ)*x))-Real.sin x*Real.sin ((n:ℝ)*x)
def rawSine (q : Tuning) (n : ℤ) (x : ℝ) : ℝ :=
  Real.sin ((n:ℝ)*x)*q.Xi (Real.cos x)-Real.cos ((n:ℝ)*x)*Real.sin x

theorem lag_eq_raw (q : Tuning) (n : ℤ) (ω : Frequency) :
    (tuningCurve q).lag n ω=rawLag q n ω/q.angleRadius ω := by
  simp only [Curve.lag,tuningCurve_apply,Real.cos_sub,q.cos_angle ω.property,
    q.sin_angle ω.property]
  dsimp [rawLag]
  ring

theorem sine_eq_raw (q : Tuning) (n : ℤ) (ω : Frequency) :
    Real.sin ((n:ℝ)*(ω:ℝ)-q.angle ω)=rawSine q n ω/q.angleRadius ω := by
  rw [Real.sin_sub,q.cos_angle ω.property,q.sin_angle ω.property]
  dsimp [rawSine]
  ring

theorem minimizer_eq_raw (q : Tuning) (ω : Frequency) :
    (tuningCurve q).minimizer ω=q.Xi (Real.cos (ω:ℝ))/q.angleRadius ω :=
  q.cos_angle ω.property

theorem radius_positive (q : Tuning) (ω : Frequency) : 0<q.angleRadius ω :=
  q.angleRadius_pos ω.property

end polyak.CertifiedExamples.Exact313

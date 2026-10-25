import polyak.Spectral.Coordinates
import polyak.General.AngleSource

/-! The closed frequency interval and the arbitrary curves of Definition FP.
Integer lags retain both the lower and upper constraints. -/
noncomputable section
namespace polyak.Levels

abbrev Frequency := Spectral.Angle

def frequencyZero : Frequency := ⟨0, by constructor <;> positivity⟩
def frequencyPi : Frequency := ⟨Real.pi, Real.pi_pos.le, le_rfl⟩

structure Curve where
  toFun : Frequency → ℝ
  continuous_toFun : Continuous toFun
  pos : ∀ ω, 0 < toFun ω
  le_pi : ∀ ω, toFun ω ≤ Real.pi
  at_zero : toFun frequencyZero = Real.pi
  at_pi : toFun frequencyPi = Real.pi

instance : CoeFun Curve (fun _ => Frequency → ℝ) := ⟨Curve.toFun⟩

namespace Curve

@[ext] theorem ext {Θ Ψ : Curve} (h : ∀ω,Θ ω=Ψ ω) : Θ=Ψ := by
  cases Θ with
  | mk f hf hp hle h0 hpi =>
    cases Ψ with
    | mk g hg hgp hgle hg0 hgpi =>
      have he : f=g := funext h
      subst g
      rfl

theorem continuous (Θ : Curve) : Continuous (Θ : Frequency → ℝ) := Θ.continuous_toFun

def lag (Θ : Curve) (n : ℤ) (ω : Frequency) : ℝ :=
  Real.cos (Θ ω) - Real.cos ((n:ℝ)*(ω:ℝ)-Θ ω)

def minimizer (Θ : Curve) (ω : Frequency) : ℝ := Real.cos (Θ ω)

theorem continuous_lag (Θ : Curve) (n : ℤ) : Continuous (Θ.lag n) := by
  exact (Real.continuous_cos.comp Θ.continuous).sub
    (Real.continuous_cos.comp ((continuous_const.mul continuous_subtype_val).sub Θ.continuous))

theorem continuous_minimizer (Θ : Curve) : Continuous Θ.minimizer := Real.continuous_cos.comp Θ.continuous

@[simp] theorem lag_zero (Θ : Curve) (ω : Frequency) : Θ.lag 0 ω = 0 := by
  simp [lag]

@[simp] theorem lag_at_zero (Θ : Curve) (n : ℤ) : Θ.lag n frequencyZero = 0 := by
  simp [lag,frequencyZero]

@[simp] theorem minimizer_at_zero (Θ : Curve) : Θ.minimizer frequencyZero = -1 := by
  simp [minimizer,Θ.at_zero]

@[simp] theorem minimizer_at_pi (Θ : Curve) : Θ.minimizer frequencyPi = -1 := by
  simp [minimizer,Θ.at_pi]

theorem lag_expand (Θ : Curve) (n : ℤ) (ω : Frequency) :
    Θ.lag n ω = Real.cos (Θ ω)*(1-Real.cos ((n:ℝ)*(ω:ℝ))) -
      Real.sin (Θ ω)*Real.sin ((n:ℝ)*(ω:ℝ)) := by
  dsimp [lag]
  rw [Real.cos_sub]
  ring

theorem lag_sine (Θ : Curve) (n : ℤ) (ω : Frequency) :
    Θ.lag n ω = 2*Real.sin ((n:ℝ)*(ω:ℝ)/2)*
      Real.sin ((n:ℝ)*(ω:ℝ)/2-Θ ω) := by
  rw [lag,Real.two_mul_sin_mul_sin]
  ring_nf

theorem lag_at_pi (Θ : Curve) (n : ℤ) :
    Θ.lag n frequencyPi = -1+Real.cos ((n:ℝ)*Real.pi) := by
  change Real.cos (Θ frequencyPi) - Real.cos ((n:ℝ)*Real.pi-Θ frequencyPi)=_
  rw [Θ.at_pi,Real.cos_pi]
  rw [Real.cos_sub,Real.cos_pi,Real.sin_pi]
  ring

theorem lag_at_pi_nonpos (Θ : Curve) (n : ℤ) : Θ.lag n frequencyPi ≤ 0 := by
  rw [lag_at_pi]
  linarith [Real.cos_le_one ((n:ℝ)*Real.pi)]

end Curve

def tuningCurve (q : General.Tuning) : Curve where
  toFun ω := q.angle ω
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp q.angle_continuousOn
  pos ω := by
    rcases eq_or_lt_of_le ω.property.1 with h | h
    · simpa [← h,q.angle_zero] using Real.pi_pos
    rcases eq_or_lt_of_le ω.property.2 with hp | hp
    · simpa [hp,q.angle_pi] using Real.pi_pos
    exact (q.angle_mem ⟨h,hp⟩).1
  le_pi ω := Real.arccos_le_pi _
  at_zero := q.angle_zero
  at_pi := q.angle_pi

@[simp] theorem tuningCurve_apply (q : General.Tuning) (ω : Frequency) :
    tuningCurve q ω = q.angle ω := rfl

end polyak.Levels

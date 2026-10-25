import polyak.Levels.Program.PinningWithin
import polyak.Levels.Geometry.JointAnalytic

/-! Literal pinning differences and slopes of the two special fan classes. -/
noncomputable section
namespace polyak.Farey.Pinning
open Levels

def period (K p:ℕ) : ℕ:=p*K+1

def realLag (θ:ℝ→ℝ) (n:ℤ) (x:ℝ) : ℝ:=Real.cos (θ x)-Real.cos ((n:ℝ)*x-θ x)

def differenceD (K p:ℕ) (θ:ℝ→ℝ) (x:ℝ) : ℝ:=
  realLag θ (-((p:ℤ)*K)) x-realLag θ 1 x

def differenceE (K p:ℕ) (θ:ℝ→ℝ) (x:ℝ) : ℝ:=
  realLag θ (((p:ℤ)-1)*K+1) x-realLag θ (-(K:ℤ)) x

theorem fan_congruences (K p:ℕ) :
    -((p:ℤ)*K)=1+(-1:ℤ)*(period K p) ∧
      ((p:ℤ)-1)*K+1= -(K:ℤ)+(1:ℤ)*(period K p) := by
  unfold period
  push_cast
  constructor <;> ring

theorem differenceD_grid (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    (θ:ℝ→ℝ) : differenceD K p θ ω=0 := by
  unfold differenceD realLag
  rw [(fan_congruences K p).1,cos_lag_add_mul_grid hω]
  simp only [Int.cast_one,one_mul,sub_self]

theorem differenceE_grid (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    (θ:ℝ→ℝ) : differenceE K p θ ω=0 := by
  unfold differenceE realLag
  rw [(fan_congruences K p).2,cos_lag_add_mul_grid hω]
  simp only [sub_self]

theorem hasDerivAt_differenceD (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    {θ:ℝ→ℝ} {d:ℝ} (hd:HasDerivAt θ d (ω:ℝ)) :
    HasDerivAt (differenceD K p θ)
      (-(period K p:ℝ)*Real.sin ((ω:ℝ)-θ ω)) (ω:ℝ) := by
  have hn:=hasDerivAt_lag_phase hd (-((p:ℤ)*K))
  have h1:=hasDerivAt_lag_phase hd 1
  have hh:=hn.sub h1
  change HasDerivAt (differenceD K p θ) _ _ at hh
  rw [(fan_congruences K p).1,sin_lag_add_mul_grid hω] at hh
  simp only [Int.cast_add,Int.cast_one,Int.cast_mul,Int.cast_neg,Int.cast_natCast,one_mul] at hh
  convert hh using 1
  ring

theorem hasDerivAt_differenceE (K p:ℕ) {ω:Frequency} (hω:ω∈periodicGrid (period K p))
    {θ:ℝ→ℝ} {d:ℝ} (hd:HasDerivAt θ d (ω:ℝ)) :
    HasDerivAt (differenceE K p θ)
      (-(period K p:ℝ)*Real.sin ((K:ℝ)*(ω:ℝ)+θ ω)) (ω:ℝ) := by
  have hn:=hasDerivAt_lag_phase hd (((p:ℤ)-1)*K+1)
  have h1:=hasDerivAt_lag_phase hd (-(K:ℤ))
  have hh:=hn.sub h1
  change HasDerivAt (differenceE K p θ) _ _ at hh
  rw [(fan_congruences K p).2,sin_lag_add_mul_grid hω] at hh
  simp only [Int.cast_add,Int.cast_neg,Int.cast_natCast,one_mul] at hh
  have he : -(K:ℝ)*(ω:ℝ)-θ ω= -((K:ℝ)*(ω:ℝ)+θ ω):=by ring
  rw [he,Real.sin_neg] at hh
  convert hh using 1
  ring

/-- The congruent lag constraints are literally the same integrals on every
periodic spectrum; no atomic representation of the measure is required. -/
theorem periodic_integral_lag_D (Θ:Curve) (K p:ℕ) (w:MeasureTheory.Measure Frequency)
    (hw:∀ᵐω∂w,ω∈periodicGrid (period K p)) :
    (∫ω,Θ.lag (-((p:ℤ)*K)) ω ∂w)=∫ω,Θ.lag 1 ω ∂w := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hw] with ω hω
  rw [(fan_congruences K p).1,lag_add_mul_grid Θ hω]

theorem periodic_integral_lag_E (Θ:Curve) (K p:ℕ) (w:MeasureTheory.Measure Frequency)
    (hw:∀ᵐω∂w,ω∈periodicGrid (period K p)) :
    (∫ω,Θ.lag (((p:ℤ)-1)*K+1) ω ∂w)=∫ω,Θ.lag (-(K:ℤ)) ω ∂w := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hw] with ω hω
  rw [(fan_congruences K p).2,lag_add_mul_grid Θ hω]

end polyak.Farey.Pinning

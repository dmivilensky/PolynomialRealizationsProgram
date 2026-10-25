import polyak.General.Angle
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Exact differential geometry of the quadratic cotangent profile.
The second derivative is an identity; strict concavity follows from the
source endpoint signs and the nonpositive quadratic coefficient. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set

def polyCotangent (a b c ω : ℝ) : ℝ :=
  (a+b*Real.cos ω+c*(Real.cos ω)^2)/Real.sin ω

def polyCotangentFirst (a b c ω : ℝ) : ℝ :=
  (-b-(a+2*c)*Real.cos ω+c*(Real.cos ω)^3)/(Real.sin ω)^2

def polyCotangentSecond (a b c ω : ℝ) : ℝ :=
  (a*(1+(Real.cos ω)^2)+2*b*Real.cos ω+
    c*((Real.cos ω)^4-(Real.cos ω)^2+2))/(Real.sin ω)^3

theorem hasDerivAt_polyCotangent (a b c : ℝ) {ω : ℝ} (hs : Real.sin ω≠0) :
    HasDerivAt (polyCotangent a b c) (polyCotangentFirst a b c ω) ω := by
  have hP : HasDerivAt (fun x=>a+b*Real.cos x+c*(Real.cos x)^2)
      (b*(-Real.sin ω)+c*(2*Real.cos ω*(-Real.sin ω))) ω := by
    convert (((Real.hasDerivAt_cos ω).const_mul b).const_add a).add
      (((Real.hasDerivAt_cos ω).pow 2).const_mul c) using 1
    ring
  unfold polyCotangent polyCotangentFirst
  convert hP.div (Real.hasDerivAt_sin ω) hs using 1
  field_simp
  linear_combination (b+2*c*Real.cos ω)*(Real.sin_sq_add_cos_sq ω)

theorem hasDerivAt_polyCotangentFirst (a b c : ℝ) {ω : ℝ} (hs : Real.sin ω≠0) :
    HasDerivAt (polyCotangentFirst a b c) (polyCotangentSecond a b c ω) ω := by
  have hN : HasDerivAt (fun x=> -b-(a+2*c)*Real.cos x+c*(Real.cos x)^3)
      ((a+2*c)*Real.sin ω-c*(3*(Real.cos ω)^2*Real.sin ω)) ω := by
    convert (((Real.hasDerivAt_cos ω).const_mul (a+2*c)).const_sub (-b)).add
      (((Real.hasDerivAt_cos ω).pow 3).const_mul c) using 1
    ring
  unfold polyCotangentFirst polyCotangentSecond
  convert hN.div ((Real.hasDerivAt_sin ω).pow 2) (pow_ne_zero 2 hs) using 1
  simp only [Pi.pow_apply]
  field_simp
  have htrig:=Real.sin_sq_add_cos_sq ω
  norm_num only [Nat.reduceSub,Nat.cast_ofNat,pow_one]
  linear_combination -(a+2*c-3*c*(Real.cos ω)^2)*Real.sin ω*htrig

/-- The exact endpoint expression in Theorem convex. -/
theorem polyCotangentSecond_endpoint_identity (a b c ω : ℝ) (hs : Real.sin ω≠0) :
    polyCotangentSecond a b c ω*(Real.sin ω)^3=
      (1/2:ℝ)*(1+Real.cos ω)^2*(a+b+c)+
      (1/2:ℝ)*(1-Real.cos ω)^2*(a-b+c)+c*(1-(Real.cos ω)^2)^2 := by
  unfold polyCotangentSecond
  field_simp
  ring

theorem polyCotangentSecond_neg {a b c ω : ℝ} (hplus : a+b+c<0)
    (hminus : a-b+c<0) (hc : c≤0) (hω : ω∈Ioo 0 Real.pi) :
    polyCotangentSecond a b c ω<0 := by
  have hs:=Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hcos : -1<Real.cos ω := by
    have hc:=Real.strictAntiOn_cos ⟨hω.1.le,hω.2.le⟩ ⟨Real.pi_pos.le,le_rfl⟩ hω.2
    simpa only [Real.cos_pi] using hc
  have hfirst : (1/2:ℝ)*(1+Real.cos ω)^2*(a+b+c)<0 :=
    mul_neg_of_pos_of_neg (mul_pos (by norm_num) (sq_pos_of_pos (by linarith))) hplus
  have hsecond : (1/2:ℝ)*(1-Real.cos ω)^2*(a-b+c)≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hminus.le
  have hthird : c*(1-(Real.cos ω)^2)^2≤0 := mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _)
  have he:=polyCotangentSecond_endpoint_identity a b c ω hs.ne'
  have hpower : 0<(Real.sin ω)^3 := pow_pos hs 3
  nlinarith

end polyak.Levels.Geometry

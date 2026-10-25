import polyak.Boundary.P5.DividedSlacks
import polyak.Boundary.P5.Tail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: (centralbounds), the genuine local limits along the blown-up branch.
Use: the strict critical constants give a common small interval for the tail.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral Filter
open scoped Topology

/-- Article: the actual twist on a blown-up coordinate tuple. -/
def branchU (h : ℝ) (Z : Coordinates) : ℝ := 1/2+h*Z 0
/-- Article: the actual main frequency on a blown-up coordinate tuple. -/
def branchX (h : ℝ) (Z : Coordinates) : ℝ := -1/2+h*Z 1
/-- Article: the actual averaged minimizer gap on a blown-up coordinate tuple. -/
def branchGap (h : ℝ) (Z : Coordinates) : ℝ :=
  (1-h*Z 3)*g (branchU h Z) (branchX h Z)+h*Z 3*g (branchU h Z) (Z 2)
/-- Article: the exact coefficient of h in the main gap difference. -/
def mainGapCoefficient (h : ℝ) (Z : Coordinates) : ℝ := Z 1-Z 0-h*((Z 0)^2+(Z 1)^2)
/-- Article: the exact coefficient of h in the averaged gap difference. -/
def meanGapCoefficient (h : ℝ) (Z : Coordinates) : ℝ :=
  mainGapCoefficient h Z+Z 3*(g (branchU h Z) (Z 2)-g (branchU h Z) (branchX h Z))

/-- Article: exact first-order main gap identity, with the full remainder retained. -/
theorem main_gap_difference (h : ℝ) (Z : Coordinates) :
    g (branchU h Z) (branchX h Z)-1/2=h*mainGapCoefficient h Z := by
  unfold g branchU branchX mainGapCoefficient
  ring

/-- Article: exact first-order mean gap identity, with the full remainder retained. -/
theorem mean_gap_difference (h : ℝ) (Z : Coordinates) :
    branchGap h Z-1/2=h*meanGapCoefficient h Z := by
  unfold branchGap meanGapCoefficient mainGapCoefficient branchU branchX g
  ring

/-- Article: the critical average-gap first-order coefficient has a strict margin. -/
theorem critical_meanGapCoefficient : |meanGapCoefficient 0 criticalPoint|<2 := by
  have hA := A₀_bounds
  have hB := B₀_bounds
  have hP := P₀_bounds
  have hy := y₀_bounds
  have hy2 : 0≤(1/4 : ℝ)-y₀^2 ∧ (1/4 : ℝ)-y₀^2≤1/4 := by
    constructor
    · nlinarith [sq_nonneg (y₀-(1/4 : ℝ))]
    · nlinarith [sq_nonneg y₀]
  have hprod := mul_nonneg hP.1.le hy2.1
  have hprod' := mul_le_mul hP.2.le hy2.2 hy2.1 (by norm_num : (0 : ℝ)≤258/100)
  rw [abs_lt]
  norm_num [meanGapCoefficient,mainGapCoefficient,branchU,branchX,g]
  constructor <;> nlinarith

/-- Article: strict derivative bounds turn into uniform relative error bounds. -/
theorem eventually_abs_difference_lt {f : ℝ → ℝ} {a K : ℝ}
    (hf : HasDerivAt f a 0) (ha : |a|<K) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), |f h-f 0|<K*h := by
  have ht : Tendsto (fun h => |(f h-f 0)/h|) (𝓝[>] (0 : ℝ)) (𝓝 |a|) := by
    simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hf.tendsto_slope_zero_right.abs
  have he := ht.eventually (eventually_lt_nhds ha)
  filter_upwards [he,self_mem_nhdsWithin] with h he hh
  rw [abs_div,show |h|=h from abs_of_pos hh] at he
  exact (div_lt_iff₀ hh).mp he

/-- Article: the actual derivative of the blown-up twist. -/
theorem branchU_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) : HasDerivAt (fun h => branchU h (Z h)) A₀ 0 := by
  have hz := (continuous_apply (0 : Fin 7)).continuousAt.comp hZ
  simpa [branchU,hZ0] using (parameter_mul_hasDerivAt hz).const_add (1/2)

/-- Article: the actual derivative of the blown-up main frequency. -/
theorem branchX_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) : HasDerivAt (fun h => branchX h (Z h)) B₀ 0 := by
  have hz := (continuous_apply (1 : Fin 7)).continuousAt.comp hZ
  simpa [branchX,hZ0] using (parameter_mul_hasDerivAt hz).const_add (-1/2)

/-- Article: the critical square-root normalization in phase and amplitude. -/
theorem sqrt_cycle : Real.sqrt (1-(-1/2 : ℝ)^2)=Real.sqrt 3/2 := by
  norm_num [show 1-(-1/2 : ℝ)^2=3/4 by norm_num,Real.sqrt_div]

/-- Article: the exact critical phase derivative. -/
theorem branch_phase_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) :
    HasDerivAt (fun h => Real.arccos (branchX h (Z h))) (-2*B₀/Real.sqrt 3) 0 := by
  have hx := branchX_hasDerivAt hZ hZ0
  have ho := (Real.hasDerivAt_arccos (x:=branchX 0 (Z 0)) (by norm_num [branchX])
    (by norm_num [branchX])).comp 0 hx
  convert ho using 1
  · rfl
  · norm_num only [branchX,zero_mul,add_zero]
    rw [show Real.sqrt (3/4 : ℝ)=Real.sqrt 3/2 by norm_num [Real.sqrt_div]]
    have hne : Real.sqrt 3≠0 := by positivity
    field_simp [hne]

/-- Article: the exact critical amplitude derivative. -/
theorem branch_amplitude_hasDerivAt {Z : ℝ → Coordinates} (hZ : ContinuousAt Z 0)
    (hZ0 : Z 0=criticalPoint) :
    HasDerivAt (fun h => 2*branchU h (Z h)*Real.sin (Real.arccos (branchX h (Z h))))
      ((3*A₀+B₀)/Real.sqrt 3) 0 := by
  have hu := branchU_hasDerivAt hZ hZ0
  have hx := branchX_hasDerivAt hZ hZ0
  have hs := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hx.pow 2)).sqrt (by norm_num [branchX])
  have hf := (hu.const_mul 2).mul hs
  convert hf using 1
  · funext h
    rw [Real.sin_arccos]
    rfl
  · dsimp only [Pi.sub_apply,Pi.pow_apply]
    norm_num only [branchU,branchX,zero_mul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,sqrt_cycle]
    rw [show Real.sqrt (3/4 : ℝ)=Real.sqrt 3/2 by norm_num [Real.sqrt_div]]
    have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
    have hne : Real.sqrt 3≠0 := by positivity
    field_simp [hne]
    nlinarith [congrArg (fun z : ℝ => A₀*z) hsq]

/-- Article: the strict source phase margin follows from the checked critical data. -/
theorem critical_phase_derivative : |-2*B₀/Real.sqrt 3|<(1/3 : ℝ) := by
  have hs : 0<Real.sqrt 3 := by positivity
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  rw [abs_div,abs_of_pos hs,div_lt_iff₀ hs]
  have ha := sq_abs (-2*B₀)
  nlinarith [critical_local_limits.2.1,abs_nonneg (-2*B₀)]

/-- Article: the strict source amplitude margin follows from the checked critical data. -/
theorem critical_amplitude_derivative : |(3*A₀+B₀)/Real.sqrt 3|<2 := by
  have hs : 0<Real.sqrt 3 := by positivity
  have hsq : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  rw [abs_div,abs_of_pos hs,div_lt_iff₀ hs]
  have ha := sq_abs (3*A₀+B₀)
  nlinarith [critical_local_limits.2.2,abs_nonneg (3*A₀+B₀)]

/-- Article: the charge's apparent 0/0 is exactly a continuous vanishing function. -/
def regularCharge (h : ℝ) (D : ℝ) : ℝ := Real.sqrt h*D/Real.sqrt (h+2)

/-- Article: the actual normalized charge equals its continuous regular form for h>0. -/
theorem charge_eq_regular {h : ℝ} (hh : 0<h) (D : ℝ) :
    h*D/Real.sinh (Real.arcosh (1+h))=regularCharge h D := by
  rw [Real.sinh_arcosh (by linarith)]
  rw [show (1+h)^2-1=h*(h+2) by ring,Real.sqrt_mul hh.le]
  have hh0 : Real.sqrt h≠0 := (Real.sqrt_pos.mpr hh).ne'
  have hh2 : Real.sqrt (h+2)≠0 := by positivity
  unfold regularCharge
  apply (div_eq_div_iff (mul_ne_zero hh0 hh2) hh2).mpr
  have hs := Real.sq_sqrt hh.le
  calc
    h*D*Real.sqrt (h+2)=(Real.sqrt h)^2*D*Real.sqrt (h+2) := by rw [hs]
    _ = Real.sqrt h*D*(Real.sqrt h*Real.sqrt (h+2)) := by ring

end polyak.Boundary.P5

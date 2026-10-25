import polyak.FareyPlateau.FanAnalysis.FiniteTests
import polyak.Levels.Chart.Coefficients

/-! A single ambient analytic family for the fixed adjacent-lag interval.
Only the three polynomial coefficients vary. This supplies the genuine
parameter regularity needed by the compact-uniform fan theorem. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Parameters
open General Levels
abbrev Point := Fin 3 → ℝ

def coordinates (q : Tuning) : Point :=
  ![(Chart.coefficients q).c0,(Chart.coefficients q).c1,(Chart.coefficients q).c2]

theorem continuous_coordinates : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Chart.Coefficients.continuous_c0.comp Chart.continuous_coefficients
  · exact Chart.Coefficients.continuous_c1.comp Chart.continuous_coefficients
  · exact Chart.Coefficients.continuous_c2.comp Chart.continuous_coefficients

def cot (p : Point) (ω : ℝ) : ℝ := Geometry.polyCotangent (p 0) (p 1) (p 2) ω
def cotFirst (p : Point) (ω : ℝ) : ℝ := Geometry.polyCotangentFirst (p 0) (p 1) (p 2) ω
def cotSecond (p : Point) (ω : ℝ) : ℝ := Geometry.polyCotangentSecond (p 0) (p 1) (p 2) ω

def gamma (k : ℕ) : ℝ := Real.pi/k
def omega (j k : ℕ) : ℝ := 2*Real.pi*j/k
def radius (k : ℕ) : ℝ := 1+(Real.cos (gamma k)/Real.sin (gamma k))^2

def first (j k : ℕ) (p : Point) : ℝ := -cotFirst p (omega j k)/radius k
def second (j k : ℕ) (p : Point) : ℝ := -cotSecond p (omega j k)/radius k+
  2*(Real.cos (gamma k)/Real.sin (gamma k))*(cotFirst p (omega j k))^2/(radius k)^2

def mix (j k : ℕ) (n : ℤ) (p : Point) : ℝ := (2*first j k p-n)/k
def curvature (j k : ℕ) (n : ℤ) (p : Point) : ℝ :=
  Real.sin (gamma k)*second j k p-(1/2 : ℝ)*Real.cos (gamma k)*(k : ℝ)^2*mix j k n p*(1-mix j k n p)
def critical (j k : ℕ) (n : ℤ) (p : Point) : ℝ :=
  -((k : ℝ)-1)*curvature j k n p/(2*(Real.sin (gamma k))^3)
def correction (j k : ℕ) (n : ℤ) (p : Point) : ℝ :=
  Fan.optimalWeight (((k : ℝ)-1)*k*Real.cos (gamma k)/4) (Real.sin (gamma k)/2)
    (2*first j k p) k (mix j k n p)

def phase (j k : ℕ) (p : Point) (e h δ : ℝ) : ℝ :=
  Geometry.arccotangent (Real.cos (gamma k)/Real.sin (gamma k)+
    cot p (omega j k+h*δ)-cot p (omega j k)-e*δ^2)

theorem analytic_coordinate (p : Point) (i : Fin 3) :
    AnalyticAt ℝ (fun p : Point => p i) p :=
  (ContinuousLinearMap.proj (R := ℝ) i).analyticAt p

theorem analytic_cot_fixed (p : Point) (ω : ℝ) : AnalyticAt ℝ (fun p => cot p ω) p := by
  exact ((analytic_coordinate p 0).add ((analytic_coordinate p 1).mul analyticAt_const)).add
    ((analytic_coordinate p 2).mul analyticAt_const) |>.div_const

theorem analytic_cotFirst (p : Point) (ω : ℝ) : AnalyticAt ℝ (fun p => cotFirst p ω) p := by
  exact (((analytic_coordinate p 1).neg.sub (((analytic_coordinate p 0).add
    (analyticAt_const.mul (analytic_coordinate p 2))).mul analyticAt_const)).add
    ((analytic_coordinate p 2).mul analyticAt_const)).div_const

theorem analytic_cotSecond (p : Point) (ω : ℝ) : AnalyticAt ℝ (fun p => cotSecond p ω) p := by
  exact ((((analytic_coordinate p 0).mul analyticAt_const).add
    ((analyticAt_const.mul (analytic_coordinate p 1)).mul analyticAt_const)).add
    ((analytic_coordinate p 2).mul analyticAt_const)).div_const

theorem analytic_first (j k : ℕ) (p : Point) : AnalyticAt ℝ (first j k) p :=
  (analytic_cotFirst p _).neg.div_const

theorem analytic_second (j k : ℕ) (p : Point) : AnalyticAt ℝ (second j k) p :=
  ((analytic_cotSecond p _).neg.div_const).add
    ((analyticAt_const.mul ((analytic_cotFirst p _).pow 2)).div_const)

theorem analytic_mix (j k : ℕ) (n : ℤ) (p : Point) : AnalyticAt ℝ (mix j k n) p :=
  ((analyticAt_const.mul (analytic_first j k p)).sub analyticAt_const).div_const

theorem analytic_curvature (j k : ℕ) (n : ℤ) (p : Point) : AnalyticAt ℝ (curvature j k n) p :=
  (analyticAt_const.mul (analytic_second j k p)).sub
    ((analyticAt_const.mul (analytic_mix j k n p)).mul (analyticAt_const.sub (analytic_mix j k n p)))

theorem analytic_critical (j k : ℕ) (n : ℤ) (p : Point) : AnalyticAt ℝ (critical j k n) p :=
  (analyticAt_const.mul (analytic_curvature j k n p)).div_const

theorem analytic_correction (j k : ℕ) (n : ℤ) (p : Point) : AnalyticAt ℝ (correction j k n) p := by
  unfold correction Fan.optimalWeight
  exact (analyticAt_const.mul ((analyticAt_const.mul (analytic_first j k p)).add
    (analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul (analytic_mix j k n p)))))).neg.div_const

theorem analytic_phase {j k : ℕ} {e : Point → ℝ} (he : ∀p, AnalyticAt ℝ e p)
    (h : ℝ) (z : Point×ℝ) (hs : Real.sin (omega j k+h*z.2) ≠ 0) :
    AnalyticAt ℝ (fun z : Point×ℝ => phase j k z.1 (e z.1) h z.2) z := by
  have hω : AnalyticAt ℝ (fun z : Point×ℝ => omega j k+h*z.2) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_snd)
  have hcos := Real.analyticAt_cos.comp hω
  have hsin := Real.analyticAt_sin.comp hω
  have hcoord (i : Fin 3) : AnalyticAt ℝ (fun z : Point×ℝ => z.1 i) z :=
    (analytic_coordinate z.1 i).comp analyticAt_fst
  have hc : AnalyticAt ℝ (fun z : Point×ℝ => cot z.1 (omega j k+h*z.2)) z :=
    (((hcoord 0).add ((hcoord 1).mul hcos)).add ((hcoord 2).mul (hcos.pow 2))).div hsin hs
  exact analyticAt_const.sub ((analyticAt_real_arctan _).comp
    ((((analyticAt_const.add hc).sub ((analytic_cot_fixed z.1 _).comp analyticAt_fst)).sub
      (((he z.1).comp analyticAt_fst).mul (analyticAt_snd.pow 2)))))

theorem continuousAt_phase {j k : ℕ} {e : Point → ℝ} (he : Continuous e)
    (h : ℝ) (z : Point×ℝ) (hs : Real.sin (omega j k+h*z.2)≠0) :
    ContinuousAt (fun z : Point×ℝ => phase j k z.1 (e z.1) h z.2) z := by
  have hω : Continuous (fun z : Point×ℝ => omega j k+h*z.2) := by fun_prop
  have hcoord (i : Fin 3) : Continuous (fun z : Point×ℝ => z.1 i) := by fun_prop
  have hc : ContinuousAt (fun z : Point×ℝ => cot z.1 (omega j k+h*z.2)) z :=
    ((((hcoord 0).add ((hcoord 1).mul (Real.continuous_cos.comp hω))).add
      ((hcoord 2).mul ((Real.continuous_cos.comp hω).pow 2))).continuousAt).div
        (Real.continuous_sin.comp hω).continuousAt hs
  have hc0 : Continuous (fun z : Point×ℝ => cot z.1 (omega j k)) := by
    unfold cot Geometry.polyCotangent
    fun_prop
  have he' : ContinuousAt (fun z : Point×ℝ => e z.1) z := (he.comp continuous_fst).continuousAt
  have hquad : ContinuousAt (fun z : Point×ℝ => z.2^2) z := by fun_prop
  exact continuousAt_const.sub (Real.continuous_arctan.continuousAt.comp
    (((continuousAt_const.add hc).sub hc0.continuousAt).sub (he'.mul hquad)))

variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem cot_actual (ω : ℝ) : cot (coordinates q) ω=Geometry.cotangent q ω := by
  rw [Geometry.cotangent_eq_poly]
  rfl

theorem first_actual : first j k (coordinates q)=Actual.first A := by
  unfold first Actual.first Geometry.shiftedFirst cotFirst radius gamma omega
  have he : Geometry.cotangent q A.frequency+A.edgeShift=Real.cos (Real.pi/k)/Real.sin (Real.pi/k) := by
    unfold Edge.AdjacentData.edgeShift Edge.shift
    ring
  rw [he]
  rfl

theorem second_actual : second j k (coordinates q)=Actual.second A := by
  unfold second Actual.second Geometry.shiftedSecond cotSecond radius gamma omega
  have he : Geometry.cotangent q A.frequency+A.edgeShift=Real.cos (Real.pi/k)/Real.sin (Real.pi/k) := by
    unfold Edge.AdjacentData.edgeShift Edge.shift
    ring
  rw [he]
  rfl

theorem mix_actual : mix j k A.lower (coordinates q)=A.mix := by
  unfold mix
  rw [first_actual A, Actual.slope A]
  have hkz : (k : ℝ)≠0 := by exact_mod_cast (show k≠0 by have := A.period_ge; omega)
  field_simp
  ring

theorem curvature_actual : curvature j k A.lower (coordinates q)=deriv^[2] A.function A.frequency := by
  unfold curvature gamma
  rw [second_actual A, mix_actual A, A.second, ← Actual.second_actual A]

theorem critical_actual : critical j k A.lower (coordinates q)=Actual.critical A := by
  unfold critical Actual.critical gamma
  rw [curvature_actual A]

theorem correction_actual : correction j k A.lower (coordinates q)=Actual.correction A := by
  unfold correction Actual.correction Actual.u Actual.v gamma
  rw [first_actual A, mix_actual A]

theorem phase_actual (e h δ : ℝ) :
    phase j k (coordinates q) e h δ=anglePath q A.edgeShift A.frequency h e δ := by
  unfold phase anglePath cotPath gamma omega
  rw [cot_actual, cot_actual]
  congr 1
  unfold Edge.AdjacentData.edgeShift Edge.shift
  have hf : (A.frequency : ℝ)=2*Real.pi*j/k := rfl
  rw [hf]
  ring

end polyak.FareyPlateau.FanAnalysis.Parameters

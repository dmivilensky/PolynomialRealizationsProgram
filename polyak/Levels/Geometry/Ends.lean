import polyak.Levels.Geometry.Arccotangent
import polyak.Levels.Geometry.ArctanAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Analytic endpoint branches of shifted curves. The branch is an actual
extension on the ambient real parameter space, rather than a derivative
of the polar arccos formula outside its closed frequency domain. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

abbrev CoefficientPoint := Fin 5→ℝ

def ambientNumerator (p : CoefficientPoint) : ℝ :=
  p 0+p 1*Real.cos (p 4)+p 2*(Real.cos (p 4))^2+p 3*Real.sin (p 4)

def ambientEndAngle (p : CoefficientPoint) : ℝ :=
  Real.pi-Real.arctan (Real.sin (p 4)/(-ambientNumerator p))

theorem analyticAt_ambientNumerator (p : CoefficientPoint) : AnalyticAt ℝ ambientNumerator p := by
  have hp (i : Fin 5) : AnalyticAt ℝ (fun z : CoefficientPoint=>z i) p :=
    (ContinuousLinearMap.proj i : CoefficientPoint→L[ℝ]ℝ).analyticAt p
  have hc:=Real.analyticAt_cos.comp (hp 4)
  have hs:=Real.analyticAt_sin.comp (hp 4)
  exact (((hp 0).add ((hp 1).mul hc)).add ((hp 2).mul (hc.pow 2))).add ((hp 3).mul hs)

/-- Joint real analyticity in all three quadratic coefficients, the shift,
and frequency wherever the endpoint denominator is nonzero. -/
theorem analyticAt_ambientEndAngle (p : CoefficientPoint) (hn : ambientNumerator p≠0) :
    AnalyticAt ℝ ambientEndAngle p := by
  have hω : AnalyticAt ℝ (fun z : CoefficientPoint=>z 4) p :=
    (ContinuousLinearMap.proj 4 : CoefficientPoint→L[ℝ]ℝ).analyticAt p
  have hquot := (Real.analyticAt_sin.comp hω).div (analyticAt_ambientNumerator p).neg (neg_ne_zero.mpr hn)
  have ha := (analyticAt_real_arctan _).comp hquot
  exact analyticAt_const.sub ha

def endAngle (q : Tuning) (s ω : ℝ) : ℝ :=
  Real.pi-Real.arctan (Real.sin ω/(-shiftNumerator q s ω))

/-- The source endpoint formula, on the actual closed-frequency branch. -/
theorem shiftedAngle_end_formula (q : Tuning) (s : ℝ) {ω : ℝ}
    (hω : ω∈Icc 0 Real.pi) (hn : shiftNumerator q s ω<0) :
    Real.pi-shiftedAngle q s ω=Real.arctan (Real.sin ω/(-shiftNumerator q s ω)) := by
  rcases eq_or_lt_of_le hω.1 with he|he
  · subst ω
    simp
  rcases eq_or_lt_of_le hω.2 with hp|hp
  · subst ω
    simp
  have hi : ω∈Ioo 0 Real.pi:=⟨he,hp⟩
  have hs:=(Real.sin_pos_of_pos_of_lt_pi he hp)
  have hu : cotangent q ω+s=shiftNumerator q s ω/Real.sin ω := by
    unfold cotangent shiftNumerator
    field_simp
  have hneg : shiftNumerator q s ω/Real.sin ω<0 := div_neg_of_neg_of_pos hn hs
  have hv : Real.sin ω/(-shiftNumerator q s ω)= -(shiftNumerator q s ω/Real.sin ω)⁻¹ := by
    field_simp
  rw [shiftedAngle_eq_arccotangent q s hi,hu,hv,Real.arctan_neg,
    Real.arctan_inv_of_neg hneg]
  unfold arccotangent
  ring

theorem endAngle_eq_shiftedAngle (q : Tuning) (s : ℝ) {ω : ℝ}
    (hω : ω∈Icc 0 Real.pi) (hn : shiftNumerator q s ω<0) :
    endAngle q s ω=shiftedAngle q s ω := by
  unfold endAngle
  rw [←shiftedAngle_end_formula q s hω hn]
  ring

theorem analyticAt_shiftNumerator (q : Tuning) (s ω : ℝ) :
    AnalyticAt ℝ (shiftNumerator q s) ω := by
  have hc:=Real.analyticAt_cos (x:=ω)
  have hs:=Real.analyticAt_sin (x:=ω)
  have he : shiftNumerator q s=(fun x=>(Chart.coefficients q).c0+
      (Chart.coefficients q).c1*Real.cos x+(Chart.coefficients q).c2*(Real.cos x)^2+s*Real.sin x) := by
    funext x
    unfold shiftNumerator
    rw [←Chart.eval_coefficients]
    rfl
  rw [he]
  exact ((analyticAt_const.add (analyticAt_const.mul hc)).add
    (analyticAt_const.mul (hc.pow 2))).add (analyticAt_const.mul hs)

theorem analyticAt_endAngle (q : Tuning) (s : ℝ) {ω : ℝ}
    (hn : shiftNumerator q s ω≠0) : AnalyticAt ℝ (endAngle q s) ω := by
  have hquot:=Real.analyticAt_sin.div (analyticAt_shiftNumerator q s ω).neg (neg_ne_zero.mpr hn)
  have ha:=(analyticAt_real_arctan _).comp hquot
  exact analyticAt_const.sub ha

@[simp] theorem endAngle_zero (q : Tuning) (s : ℝ) : endAngle q s 0=Real.pi := by simp [endAngle]
@[simp] theorem endAngle_pi (q : Tuning) (s : ℝ) : endAngle q s Real.pi=Real.pi := by simp [endAngle]

/-- The two endpoint extensions agree with the actual curve in a full
relative neighborhood, jointly in the tuning, shift and frequency. -/
theorem endAngle_eventually_eq_joint (q : Tuning) (s : ℝ) (ω : Frequency)
    (hω : ω=frequencyZero ∨ ω=frequencyPi) :
    ∀ᶠ p : Tuning×ℝ×Frequency in 𝓝 (q,s,ω),
      endAngle p.1 p.2.1 p.2.2=shiftedCurve p.1 p.2.1 p.2.2 := by
  have hn : shiftNumerator q s ω<0 := by
    rcases hω with rfl|rfl
    · simpa only [shiftNumerator,frequencyZero,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg
    · simpa only [shiftNumerator,frequencyPi,Real.cos_pi,Real.sin_pi,mul_zero,add_zero] using q.Xi_neg_one_neg
  have hcont := shiftNumerator_jointContinuous
  filter_upwards [hcont.continuousAt.eventually (eventually_lt_nhds hn)] with p hp
  exact endAngle_eq_shiftedAngle p.1 p.2.1 p.2.2.property hp

end polyak.Levels.Geometry

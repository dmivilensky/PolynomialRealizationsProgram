import polyak.Levels.Geometry.Ends
import polyak.Levels.Chart.AnalyticCoordinates

/-! One analytic continuation on an open neighborhood of every compact
source parameter set, including both frequency endpoints. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

def ambientInteriorAngle (p : CoefficientPoint) : ℝ :=
  arccotangent (ambientNumerator p/Real.sin (p 4))

def ambientAngle (p : CoefficientPoint) : ℝ :=
  if 0<Real.sin (p 4) then ambientInteriorAngle p else ambientEndAngle p

theorem ambientAngle_eq_end_of_neg {p : CoefficientPoint} (hn : ambientNumerator p<0) :
    ambientAngle p=ambientEndAngle p := by
  unfold ambientAngle
  split_ifs with hs
  · have hneg : ambientNumerator p/Real.sin (p 4)<0:=div_neg_of_neg_of_pos hn hs
    have he : Real.sin (p 4)/(-ambientNumerator p)= -(ambientNumerator p/Real.sin (p 4))⁻¹ := by field_simp
    unfold ambientInteriorAngle ambientEndAngle arccotangent
    rw [he,Real.arctan_neg,Real.arctan_inv_of_neg hneg]
    ring
  · rfl

theorem analyticAt_ambientInteriorAngle (p : CoefficientPoint) (hs : Real.sin (p 4)≠0) :
    AnalyticAt ℝ ambientInteriorAngle p := by
  have hω:=Chart.analyticAt_coordinate p 4
  have hquot:=(analyticAt_ambientNumerator p).div (Real.analyticAt_sin.comp hω) hs
  exact analyticAt_const.sub ((analyticAt_real_arctan _).comp hquot)

theorem analyticAt_ambientAngle (p : CoefficientPoint)
    (h : 0<Real.sin (p 4) ∨ ambientNumerator p<0) : AnalyticAt ℝ ambientAngle p := by
  by_cases hs : 0<Real.sin (p 4)
  · apply (analyticAt_ambientInteriorAngle p hs.ne').congr
    have hc : Continuous (fun p : CoefficientPoint=>Real.sin (p 4)):=by fun_prop
    filter_upwards [hc.continuousAt.eventually (eventually_gt_nhds hs)] with z hz
    simp only [ambientAngle,ite_eq_left hz]
  · have hn:=h.resolve_left hs
    apply (analyticAt_ambientEndAngle p hn.ne).congr
    filter_upwards [(analyticAt_ambientNumerator p).continuousAt.eventually (eventually_lt_nhds hn)] with z hz
    exact (ambientAngle_eq_end_of_neg hz).symm

def coefficientPoint (q : Tuning) (s ω : ℝ) : CoefficientPoint :=
  ![(Chart.coefficients q).c0,(Chart.coefficients q).c1,(Chart.coefficients q).c2,s,ω]

theorem ambientNumerator_coefficientPoint (q : Tuning) (s ω : ℝ) :
    ambientNumerator (coefficientPoint q s ω)=shiftNumerator q s ω := by
  change (Chart.coefficients q).c0+(Chart.coefficients q).c1*Real.cos ω+
    (Chart.coefficients q).c2*(Real.cos ω)^2+s*Real.sin ω=q.Xi (Real.cos ω)+s*Real.sin ω
  rw [←Chart.eval_coefficients]
  rfl

theorem ambientAngle_coefficientPoint (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    ambientAngle (coefficientPoint q s ω)=shiftedAngle q s ω := by
  by_cases hs : 0<Real.sin ω
  · change (if 0<Real.sin ω then ambientInteriorAngle (coefficientPoint q s ω) else _)=_
    rw [ite_eq_left hs]
    unfold ambientInteriorAngle
    rw [ambientNumerator_coefficientPoint]
    have hi : ω∈Ioo 0 Real.pi := by
      constructor
      · by_contra hn
        have he:ω=0:=le_antisymm (le_of_not_gt hn) hω.1
        simp only [he,Real.sin_zero,lt_self_iff_false] at hs
      · by_contra hn
        have he:ω=Real.pi:=le_antisymm hω.2 (le_of_not_gt hn)
        simp only [he,Real.sin_pi,lt_self_iff_false] at hs
    rw [shiftedAngle_eq_arccotangent q s hi]
    congr 1
    change shiftNumerator q s ω/Real.sin ω=cotangent q ω+s
    unfold shiftNumerator cotangent
    field_simp
  · have hn : shiftNumerator q s ω<0 := by
      rcases eq_or_lt_of_le hω.1 with he|he
      · rw [←he]
        simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg
      · have hp : ω=Real.pi := by
          by_contra hn
          exact hs (Real.sin_pos_of_pos_of_lt_pi he (lt_of_le_of_ne hω.2 hn))
        rw [hp]
        simpa only [shiftNumerator,Real.cos_pi,Real.sin_pi,mul_zero,add_zero] using q.Xi_neg_one_neg
    rw [ambientAngle_eq_end_of_neg (by rw [ambientNumerator_coefficientPoint]; exact hn)]
    change Real.pi-Real.arctan (Real.sin ω/(-ambientNumerator (coefficientPoint q s ω)))=shiftedAngle q s ω
    rw [ambientNumerator_coefficientPoint]
    exact endAngle_eq_shiftedAngle q s hω hn

/-- This single function is defined on the ambient source coordinates
(kappa,y,beta,shift,frequency), independently of the tuning subtype. -/
def jointAngle (p : Chart.AmbientPoint) : ℝ := ambientAngle (Chart.rawToCoefficient p)

theorem jointAngle_actual (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    jointAngle ![q.kappa,q.y,q.beta,s,ω]=shiftedAngle q s ω := by
  unfold jointAngle
  rw [Chart.rawToCoefficient_actual]
  exact ambientAngle_coefficientPoint q s hω

theorem analyticAt_jointAngle_actual (q : Tuning) (s : ℝ) {ω : ℝ} (hω : ω∈Icc 0 Real.pi) :
    AnalyticAt ℝ jointAngle ![q.kappa,q.y,q.beta,s,ω] := by
  have hpoint : AnalyticAt ℝ ambientAngle (Chart.rawToCoefficient ![q.kappa,q.y,q.beta,s,ω]) := by
    rw [Chart.rawToCoefficient_actual]
    apply analyticAt_ambientAngle
    by_cases hs : 0<Real.sin ω
    · exact Or.inl hs
    · right
      change ambientNumerator (coefficientPoint q s ω)<0
      rw [ambientNumerator_coefficientPoint]
      rcases eq_or_lt_of_le hω.1 with he|he
      · rw [←he]
        simpa only [shiftNumerator,Real.cos_zero,Real.sin_zero,mul_zero,add_zero] using q.Xi_one_neg
      · have hp : ω=Real.pi := by
          by_contra hn
          exact hs (Real.sin_pos_of_pos_of_lt_pi he (lt_of_le_of_ne hω.2 hn))
        rw [hp]
        simpa only [shiftNumerator,Real.cos_pi,Real.sin_pi,mul_zero,add_zero] using q.Xi_neg_one_neg
  exact hpoint.comp (Chart.analyticAt_rawToCoefficient_actual q s ω)

/-- Literal ambient analytic extension around every compact subset of
D × R × [0,pi]. In fact the same open analytic locus works for all of them. -/
theorem joint_analytic_extension :
    ∃U : Set Chart.AmbientPoint,IsOpen U ∧ AnalyticOnNhd ℝ jointAngle U ∧
      (∀q : Tuning,∀s : ℝ,∀ω∈Icc 0 Real.pi,![q.kappa,q.y,q.beta,s,ω]∈U) ∧
      ∀q : Tuning,∀s : ℝ,∀ω∈Icc 0 Real.pi,
        jointAngle ![q.kappa,q.y,q.beta,s,ω]=shiftedAngle q s ω := by
  exact ⟨{p | AnalyticAt ℝ jointAngle p},isOpen_analyticAt ℝ jointAngle,
    fun _ hp=>hp,fun q s _ hω=>analyticAt_jointAngle_actual q s hω,
    fun q s _ hω=>jointAngle_actual q s hω⟩

end polyak.Levels.Geometry

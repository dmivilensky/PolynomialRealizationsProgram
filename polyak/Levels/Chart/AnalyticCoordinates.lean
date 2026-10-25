import polyak.Levels.Chart.Coefficients
import Mathlib.Analysis.Analytic.Constructions

/-! Ambient real-analytic source coordinates for the endpoint continuation.
Input coordinates are (κ,y,β,s,ω); output coordinates are (Ξ₀,Ξ₁,Ξ₂,s,ω). -/
noncomputable section
namespace polyak.Levels.Chart
open General

abbrev AmbientPoint := Fin 5→ℝ

def rawA (p : AmbientPoint) : ℝ := 1+p 2-(p 1/p 0+p 1)/2
def rawB (p : AmbientPoint) : ℝ := (p 1-p 1/p 0)/2

def rawToCoefficient (p : AmbientPoint) : AmbientPoint :=
  ![(rawB p^2-(1-p 2)^2-rawA p^2)/(2*rawB p*(1-p 2)),
    (2*rawA p*(1+p 2))/(2*rawB p*(1-p 2)),
    -4*p 2/(2*rawB p*(1-p 2)),p 3,p 4]

theorem analyticAt_coordinate (p : AmbientPoint) (i : Fin 5) :
    AnalyticAt ℝ (fun p : AmbientPoint => p i) p :=
  (ContinuousLinearMap.proj (R := ℝ) i).analyticAt p

theorem analyticAt_rawA (p : AmbientPoint) (hk : p 0≠0) : AnalyticAt ℝ rawA p := by
  exact (analyticAt_const.add (analyticAt_coordinate p 2)).sub
    (((analyticAt_coordinate p 1).div (analyticAt_coordinate p 0) hk).add
      (analyticAt_coordinate p 1)).div_const

theorem analyticAt_rawB (p : AmbientPoint) (hk : p 0≠0) : AnalyticAt ℝ rawB p := by
  exact ((analyticAt_coordinate p 1).sub
    ((analyticAt_coordinate p 1).div (analyticAt_coordinate p 0) hk)).div_const

theorem analyticAt_rawToCoefficient (p : AmbientPoint) (hk : p 0≠0)
    (hB : rawB p≠0) (hβ : 1-p 2≠0) : AnalyticAt ℝ rawToCoefficient p := by
  have ha := analyticAt_rawA p hk
  have hb := analyticAt_rawB p hk
  have hβa : AnalyticAt ℝ (fun p : AmbientPoint => 1-p 2) p :=
    analyticAt_const.sub (analyticAt_coordinate p 2)
  have hd : AnalyticAt ℝ (fun p : AmbientPoint => 2*rawB p*(1-p 2)) p :=
    (analyticAt_const.mul hb).mul hβa
  have hdn : 2*rawB p*(1-p 2)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hB) hβ
  have h0 := (((hb.pow 2).sub (hβa.pow 2)).sub (ha.pow 2)).div hd hdn
  have h1 : AnalyticAt ℝ (fun p : AmbientPoint => 2*rawA p*(1+p 2)/(2*rawB p*(1-p 2))) p := ((analyticAt_const.mul ha).mul
    (analyticAt_const.add (analyticAt_coordinate p 2))).div hd hdn
  have h2 : AnalyticAt ℝ (fun p : AmbientPoint => -4*p 2/(2*rawB p*(1-p 2))) p := (analyticAt_const.mul (analyticAt_coordinate p 2)).div hd hdn
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact analyticAt_coordinate p 3
  · exact analyticAt_coordinate p 4

theorem rawToCoefficient_actual (q : Tuning) (s ω : ℝ) :
    rawToCoefficient ![q.kappa,q.y,q.beta,s,ω]=
      ![(coefficients q).c0,(coefficients q).c1,(coefficients q).c2,s,ω] := by
  rfl

theorem analyticAt_rawToCoefficient_actual (q : Tuning) (s ω : ℝ) :
    AnalyticAt ℝ rawToCoefficient ![q.kappa,q.y,q.beta,s,ω] := by
  apply analyticAt_rawToCoefficient
  · exact ne_of_gt q.kappa_pos
  · exact q.B_ne_zero
  · exact ne_of_gt (sub_pos.mpr q.beta_lt_one)

end polyak.Levels.Chart

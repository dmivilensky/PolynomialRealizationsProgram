import polyak.Farey.Examples.ThirteenContracts

/-! Exact gap membership of both rational examples. Only rational inequalities
and the algebraic formula for cos(2*pi/5) are used. -/
noncomputable section
namespace polyak.CertifiedExamples.Rational
open polyak.Farey.Examples polyak.Levels

private theorem three_tenths_lt_cos_fifth : (3:ℝ)/10<Real.cos (2*Real.pi/5) := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hn:=Real.sqrt_nonneg (5:ℝ)
  have hcos : Real.cos (2*Real.pi/5)=2*((1+Real.sqrt 5)/4)^2-1 := by
    rw [show 2*Real.pi/5=2*(Real.pi/5) by ring,Real.cos_two_mul,Real.cos_pi_div_five]
  rw [hcos]
  nlinarith

private theorem boundary_four : Chart.boundaryCosine 4=0 := by
  unfold Chart.boundaryCosine Chart.boundaryAngle
  norm_num [show 2*Real.pi/(4:ℝ)=Real.pi/2 by ring,Real.cos_pi_div_two]

private theorem boundary_five : (3:ℝ)/10<Chart.boundaryCosine 5 :=
  three_tenths_lt_cos_fifth

theorem thirteen_gap_checks : GapFourChecks thirteenTuning := by
  have hcoeff : Chart.coefficients thirteenTuning=
      ⟨88897198775653/91052250190902,242832333719/122711927481,
        -26156560000/8676600933⟩ := by
    ext <;> norm_num [Chart.coefficients,General.Tuning.A,General.Tuning.B,
      General.Tuning.x,thirteenTuning]
  have hD : Chart.gapDiscriminant (Chart.coefficients thirteenTuning)=
      496431614802495393279556/737852640159007947262689 := by
    rw [hcoeff]; norm_num [Chart.gapDiscriminant]
  have hDpos : 0<Chart.gapDiscriminant (Chart.coefficients thirteenTuning) := by
    rw [hD]; norm_num
  have hs := Real.sq_sqrt hDpos.le
  have hn := Real.sqrt_nonneg (Chart.gapDiscriminant (Chart.coefficients thirteenTuning))
  have hsq : Real.sqrt (Chart.gapDiscriminant (Chart.coefficients thirteenTuning))<821/1000 := by
    rw [hD] at hs hn ⊢
    nlinarith
  unfold GapFourChecks
  refine ⟨?_,hDpos,?_,?_⟩
  · rw [hcoeff]; norm_num
  · rw [boundary_four]
    unfold Chart.leftRoot
    rw [hcoeff]
    norm_num only [Chart.Coefficients.c1,Chart.Coefficients.c2]
    rw [lt_div_iff₀ (by norm_num)]
    rw [hcoeff] at hsq
    linarith
  · apply lt_trans (b:=(3:ℝ)/10) _ boundary_five
    unfold Chart.rightRoot
    rw [hcoeff]
    norm_num only [Chart.Coefficients.c1,Chart.Coefficients.c2]
    rw [div_lt_iff₀ (by norm_num)]
    rw [hcoeff] at hsq
    linarith

theorem convergence_gap_checks : GapFourChecks convergenceTuning := by
  have hcoeff : Chart.coefficients convergenceTuning=
      ⟨203570/208791,14967/7733,-620000/208791⟩ := by
    ext <;> norm_num [Chart.coefficients,General.Tuning.A,General.Tuning.B,
      General.Tuning.x,convergenceTuning]
  have hD : Chart.gapDiscriminant (Chart.coefficients convergenceTuning)=25201041124/43593681681 := by
    rw [hcoeff]; norm_num [Chart.gapDiscriminant]
  have hDpos : 0<Chart.gapDiscriminant (Chart.coefficients convergenceTuning) := by
    rw [hD]; norm_num
  have hs := Real.sq_sqrt hDpos.le
  have hn := Real.sqrt_nonneg (Chart.gapDiscriminant (Chart.coefficients convergenceTuning))
  have hsq : Real.sqrt (Chart.gapDiscriminant (Chart.coefficients convergenceTuning))<761/1000 := by
    rw [hD] at hs hn ⊢
    nlinarith
  unfold GapFourChecks
  refine ⟨?_,hDpos,?_,?_⟩
  · rw [hcoeff]; norm_num
  · rw [boundary_four]
    unfold Chart.leftRoot
    rw [hcoeff]
    norm_num only [Chart.Coefficients.c1,Chart.Coefficients.c2]
    rw [lt_div_iff₀ (by norm_num)]
    rw [hcoeff] at hsq
    linarith
  · apply lt_trans (b:=(3:ℝ)/10) _ boundary_five
    unfold Chart.rightRoot
    rw [hcoeff]
    norm_num only [Chart.Coefficients.c1,Chart.Coefficients.c2]
    rw [div_lt_iff₀ (by norm_num)]
    rw [hcoeff] at hsq
    linarith

theorem thirteen_in_gap_four : Geometry.Gap 4 thirteenTuning := gap_four_of_checks thirteen_gap_checks

theorem convergence_in_gap_four : Geometry.Gap 4 convergenceTuning := gap_four_of_checks convergence_gap_checks

end polyak.CertifiedExamples.Rational

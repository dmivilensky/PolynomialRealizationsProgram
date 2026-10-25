import polyak.Boundary.P5.CriticalRoot

/-! A refined enclosure of the actual source quintic root for the printed
critical coefficients. Its endpoints are exact rationals. -/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Numerics LeanCert.Core

def criticalFineInterval : IntervalRat :=
  ⟨231889130449470/1000000000000000,231889130449471/1000000000000000,by norm_num⟩

theorem y₀_decimal_bounds :
    (231889130449470/1000000000000000 : ℝ)<y₀ ∧
      y₀<231889130449471/1000000000000000 := by
  have hm : StrictAntiOn (fun r : ℝ => Polynomial.aeval r criticalPolynomial)
      (Set.Icc (criticalInterval.lo : ℝ) criticalInterval.hi) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) criticalPolynomial.continuous_aeval.continuousOn
    intro r hr
    rw [(criticalPolynomial.hasDerivAt_aeval r).deriv]
    have hr' : r∈Set.Icc (criticalInterval.lo : ℝ) criticalInterval.hi := interior_subset hr
    exact critical_derivative_negative r hr'
  have hl : (231889130449470/1000000000000000 : ℝ)∈criticalInterval := by
    norm_num [criticalInterval,IntervalRat.mem_def]
  have hu : (231889130449471/1000000000000000 : ℝ)∈criticalInterval := by
    norm_num [criticalInterval,IntervalRat.mem_def]
  have hpl : 0<Polynomial.aeval (231889130449470/1000000000000000 : ℝ) criticalPolynomial := by
    norm_num [criticalPolynomial]
  have hpu : Polynomial.aeval (231889130449471/1000000000000000 : ℝ) criticalPolynomial<0 := by
    norm_num [criticalPolynomial]
  have he : Polynomial.aeval y₀ criticalPolynomial=0 := criticalRoot.root
  constructor
  · by_contra hn
    have ho:=hm.antitoneOn criticalRoot.mem hl (le_of_not_gt hn)
    change Polynomial.aeval (231889130449470/1000000000000000 : ℝ) criticalPolynomial≤
      Polynomial.aeval y₀ criticalPolynomial at ho
    rw [he] at ho
    linarith
  · by_contra hn
    have ho:=hm.antitoneOn hu criticalRoot.mem (le_of_not_gt hn)
    change Polynomial.aeval y₀ criticalPolynomial≤
      Polynomial.aeval (231889130449471/1000000000000000 : ℝ) criticalPolynomial at ho
    rw [he] at ho
    linarith

theorem y₀_fine_mem : y₀∈criticalFineInterval := by
  norm_num only [criticalFineInterval,IntervalRat.mem_def,Rat.cast_div,Rat.cast_ofNat]
  constructor <;> linarith [y₀_decimal_bounds.1,y₀_decimal_bounds.2]

end polyak.Boundary.P5

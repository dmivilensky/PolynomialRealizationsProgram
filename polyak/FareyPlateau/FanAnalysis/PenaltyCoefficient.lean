import polyak.FareyPlateau.Edge.Adjacent
import polyak.ModeLocking.Localization.QuantitativeLocking

/-! The sharp regular locking coefficient of the actual two-lag edge
certificate is exactly the printed coefficient F''/(2 sin^3 c'). -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking
open scoped BigOperators
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem adjacent_pinning_value : pinningPolynomial A.lags A.weight A.frequency=
    2*(Real.sin (Real.pi/k))^2 := by
  have hcos (n : ℤ) (hn : n∈A.lags) :
      Real.cos ((n:ℝ)*(A.frequency:ℝ))=Real.cos (2*(Real.pi/k)) := by
    have hh := (Edge.lag_trig_reduce (by have := A.period_ge; omega) A.numerator_lt.le n 0).1
    rw [A.residue n hn] at hh
    simpa only [Edge.AdjacentData.frequency,Int.cast_one,mul_one,sub_zero,
      show 2*Real.pi/k=2*(Real.pi/k) by ring] using hh
  unfold pinningPolynomial
  change (∑n∈{A.lower,A.upper},A.weight n*(1-Real.cos ((n:ℝ)*(A.frequency:ℝ))))=_
  rw [Finset.sum_pair A.lower_ne_upper,hcos A.lower (by simp [Edge.AdjacentData.lags]),
    hcos A.upper (by simp [Edge.AdjacentData.lags])]
  simp only [Edge.AdjacentData.weight,ite_true,ite_eq_right A.lower_ne_upper.symm]
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi/k)]

theorem adjacent_locking_coefficient
    (hstrict : ∀x : ℝ,0<x → x≤Real.pi → x≠(A.frequency:ℝ) → 0<A.function x)
    (hcurv : 0<deriv^[2] A.function A.frequency)
    (hend : 0<deriv^[2] A.function 0) :
    Localization.minimalLockingCoefficient (A.certificate hstrict hcurv hend).regularData=
      deriv^[2] A.function A.frequency/(2*(Real.sin (Real.pi/k))^3) := by
  let C := A.certificate hstrict hcurv hend
  let D := C.regularData
  have he (i : Fin D.d) : Localization.lockingCoefficient D i=
      deriv^[2] A.function A.frequency/(2*(Real.sin (Real.pi/k))^3) := by
    change |deriv^[2] (finiteSymbol q A.edgeShift A.lags A.weight) A.frequency| /
      (2*Real.sin (Geometry.shiftedCurve q A.edgeShift A.frequency)*
        pinningPolynomial A.lags A.weight A.frequency)=_
    rw [A.finiteSymbol_second,adjacent_pinning_value A]
    have hp : Geometry.shiftedCurve q A.edgeShift A.frequency=Real.pi/k :=
      Edge.phase_at_shift q A.period_ge
        ⟨Edge.atom_pos A.numerator_pos (by have := A.period_ge; omega) A.numerator_lt.le,
          Edge.atom_lt_pi (by have := A.period_ge; omega) A.numerator_lt⟩
    rw [hp,abs_of_neg (mul_neg_of_neg_of_pos (by norm_num : (-2:ℝ)<0) hcurv)]
    field_simp
  apply le_antisymm
  · exact (Localization.minimalLockingCoefficient_le D ⟨0,D.d_pos⟩).trans_eq (he _)
  · change _≤Localization.minimalLockingCoefficient D
    unfold Localization.minimalLockingCoefficient
    rw [Finset.le_inf'_iff]
    intro i _
    exact (he i).ge

end polyak.FareyPlateau.FanAnalysis.Actual

import polyak.ModeLocking.Regular.Threshold
import polyak.ModeLocking.Continuation.Determinant

/-! Literal shift derivative of the actual phase and of a regular dual symbol. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open General Levels
open scoped BigOperators

theorem hasDerivAt_phase_shift (q : Tuning) (s : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    HasDerivAt (fun t => Geometry.shiftedCurve q t ω)
      (-(Real.sin (Geometry.shiftedCurve q s ω)) ^ 2) s := by
  have he : (fun t => Geometry.shiftedCurve q t ω) =
      fun t => Real.pi / 2 - Real.arctan (Geometry.cotangent q ω + t) := by
    funext t
    exact Geometry.shiftedAngle_eq_arccotangent q t hω
  have hd := (((hasDerivAt_id s).const_add (Geometry.cotangent q ω)).arctan).const_sub (Real.pi / 2)
  have hs := Localization.phase_sin_pos q s ω hω
  have hc := Geometry.cot_shiftedAngle q s hω
  change Real.cos (Geometry.shiftedCurve q s ω) / Real.sin (Geometry.shiftedCurve q s ω) = _ at hc
  change Real.cos (Geometry.shiftedCurve q s ω) / Real.sin (Geometry.shiftedCurve q s ω) = Geometry.cotangent q ω + s at hc
  have hmul := (div_eq_iff hs.ne').mp hc
  have htrig := Real.sin_sq_add_cos_sq (Geometry.shiftedCurve q s ω)
  have heq : (Real.sin (Geometry.shiftedCurve q s ω)) ^ 2 * (1 + (Geometry.cotangent q ω + s) ^ 2) = 1 := by
    rw [hmul, mul_pow] at htrig
    nlinarith only [htrig]
  convert hd using 1
  · exact he
  · dsimp only [id_eq]
    field_simp
    nlinarith only [heq]

theorem hasDerivAt_lag_shift (q : Tuning) (s : ℝ) (n : ℤ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    HasDerivAt (fun t => (Geometry.shiftedCurve q t).lag n ω)
      ((Real.sin (Geometry.shiftedCurve q s ω)) ^ 2 *
        (Real.sin (Geometry.shiftedCurve q s ω) +
          Real.sin ((n : ℝ) * (ω : ℝ) - Geometry.shiftedCurve q s ω))) s := by
  have hd := hasDerivAt_phase_shift q s ω hω
  convert hd.cos.sub ((hd.const_sub ((n : ℝ) * (ω : ℝ))).cos) using 1
  · rfl
  · ring

theorem hasDerivAt_finiteSymbol_shift (q : Tuning) (s : ℝ) (N : Finset ℤ) (a : ℤ → ℝ)
    (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier)
    (hz : finiteSymbol q s N a ω = 0) :
    HasDerivAt (fun t => finiteSymbol q t N a ω)
      (Real.sin (Geometry.shiftedCurve q s ω) * pinningPolynomial N a ω) s := by
  have he : (fun t => finiteSymbol q t N a ω) =
      fun t => ∑ n ∈ N, a n * (Geometry.shiftedCurve q t).lag n ω := by
    funext t
    exact finiteSymbol_actual q t N a ω
  rw [he]
  have hd := HasDerivAt.sum (u := N) (fun n _ => (hasDerivAt_lag_shift q s n ω hω).const_mul (a n))
  convert hd using 1
  · funext t
    simp only [Finset.sum_apply]
  let θ := Geometry.shiftedCurve q s ω
  let P := pinningPolynomial N a ω
  let Q := ∑ n ∈ N, a n * Real.sin ((n : ℝ) * (ω : ℝ))
  have hzero : Real.cos θ * P - Real.sin θ * Q = 0 := by
    have hid : finiteSymbol q s N a ω = Real.cos θ * P - Real.sin θ * Q := by
      rw [finiteSymbol_actual]
      dsimp only [P, Q, pinningPolynomial]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [Curve.lag_expand]
      dsimp only [θ]
      ring
    exact hid.symm.trans hz
  have hsum : (∑ n ∈ N, a n * ((Real.sin θ)^2 *
      (Real.sin θ + Real.sin ((n : ℝ) * (ω : ℝ) - θ)))) =
      (Real.sin θ)^2 * (Real.sin θ * P + Real.cos θ * Q) := by
    dsimp [P, Q, pinningPolynomial]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Real.sin_sub]
    ring
  change Real.sin θ * P = ∑ n ∈ N, a n * ((Real.sin θ)^2 *
      (Real.sin θ + Real.sin ((n : ℝ) * (ω : ℝ) - θ)))
  rw [hsum]
  have htrig := Real.sin_sq_add_cos_sq θ
  linear_combination (Real.sin θ * Real.cos θ) * hzero - (Real.sin θ * P) * htrig

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem shift_derivative_pos (i : Fin D.d) :
    0 < deriv (fun t => finiteSymbol q t D.lags D.dual (D.atoms i)) s := by
  rw [(Continuation.hasDerivAt_finiteSymbol_shift q s D.lags D.dual (D.atoms i)
    ⟨(D.atoms_grid i).1, D.atoms_lt_pi i⟩ (D.symbol_zero_support i)).deriv]
  exact mul_pos (Localization.phase_sin_pos q s (D.atoms i)
    ⟨(D.atoms_grid i).1, D.atoms_lt_pi i⟩) (D.pinning_pos i)

end polyak.ModeLocking.RegularData

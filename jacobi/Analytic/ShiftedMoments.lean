import jacobi.Analytic.RealShiftSpectrum
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
Article: jacobi, Appendix E.1.
The actual convergent mass series has its genuine derivative throughout
the full real-shift range, and T_2(w)=-2*M'(w). A positive original pole
margin supplies a summable bound for the derivatives on an open shift
neighborhood. No finite-resolvent or numerical convergence is assumed.
Use: shiftedMass_hasDerivAt and shiftedSecond_eq_deriv identify the original off-edge mass and second-moment constraints supplied to the existing calibrations.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set

/-- The original shifted spectral mass, defined by its actual Bessel eigenvalue series.
Use: shiftedMass_hasDerivAt and shiftedSecond_eq_deriv identify the original off-edge mass and second-moment constraints supplied to the existing calibrations.
Article: jacobi, Appendix E.1.
-/
def shiftedMass (a:ℝ) (ha:-1<a) (w:ℝ) : ℝ := ∑'k,realShiftedEdge a ha w k

/-- The original second shifted spectral moment, defined by the same actual Bessel eigenvalue series.
Use: shiftedSecond_eq_deriv proves the printed derivative relation used by the real off-edge calibration bounds.
Article: jacobi, Appendix E.1.
-/
def shiftedSecond (a:ℝ) (ha:-1<a) (w:ℝ) : ℝ := ∑'k,(realShiftedEdge a ha w k)^2

/-- Every actual shifted spectral coefficient has its true real derivative above the original first pole.
Use: shiftedMass_hasDerivAt differentiates the genuine original mass series with a proved uniform summable derivative bound.
Article: jacobi, Appendix E.1.
Proof: differentiate the affine spectral denominator and its reciprocal, using its independently proved positive value. -/
theorem realShiftedEdge_hasDerivAt (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) (k:ℕ) :
    HasDerivAt (fun v:ℝ => realShiftedEdge a ha v k) (-2/(jacobi.Bessel.sigma a ha k+w)^2) w := by
  have h := (((hasDerivAt_id w).const_add (jacobi.Bessel.sigma a ha k)).inv
    (realShifted_denominator_pos a ha hw k).ne').const_mul 2
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

/-- The actual shifted spectral mass has the full printed derivative relation throughout the real physical shift range.
Use: shiftedSecond_eq_deriv provides the same actual second moment to every off-edge Young, Keller and joint calibration without an assumed interchange of the infinite series and differentiation.
Article: jacobi, Appendix E.1.
Proof: retain half the original first-pole margin on an open neighborhood of the actual shift. Every shifted denominator there is at least half its value at the center. The derivative is bounded by twice the center's actual squared edge eigenvalue, a summable sequence. Apply the community dominated series derivative theorem and factor out the exact scalar -1/2. -/
theorem shiftedMass_hasDerivAt (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    HasDerivAt (shiftedMass a ha) (-(shiftedSecond a ha w)/2) w := by
  -- The margin is taken at the actual first Bessel pole, uniformly over every original spectral index.
  let S := realShiftSpectrum a ha w hw
  let ε : ℝ := (jacobi.Bessel.sigma a ha 0+w)/2
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsum := jacobi.Continuum.summable_powers S.summable (fun k => (S.positive k).le) (show 0<2 by decide)
  have hwithin (x:ℝ) (hx:x∈Ioo (w-ε) (w+ε)) : - jacobi.Bessel.sigma a ha 0<x := by
    dsimp [ε] at hx
    linarith [hx.1]
  have hbound (k:ℕ) (x:ℝ) (hx:x∈Ioo (w-ε) (w+ε)) :
      ‖-2/(jacobi.Bessel.sigma a ha k+x)^2‖≤2*(S.value k)^2 := by
    have hden := realShifted_denominator_pos a ha hw k
    have hxden := realShifted_denominator_pos a ha (hwithin x hx) k
    have hmono := (jacobi.Bessel.sigma_strictMono ha).monotone (Nat.zero_le k)
    have hhalf : (jacobi.Bessel.sigma a ha k+w)/2≤ jacobi.Bessel.sigma a ha k+x := by
      dsimp [ε] at hx
      linarith [hx.1]
    have hsq := (sq_le_sq₀ (by positivity : 0≤(jacobi.Bessel.sigma a ha k+w)/2) hxden.le).mpr hhalf
    norm_num only [Real.norm_eq_abs,abs_div,abs_neg,abs_pow,abs_of_pos hxden,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ 2/((jacobi.Bessel.sigma a ha k+w)/2)^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
      _ = _ := by change _=2*(2/(jacobi.Bessel.sigma a ha k+w))^2; field_simp
  have h := hasDerivAt_tsum_of_isPreconnected (hsum.mul_left 2) isOpen_Ioo isPreconnected_Ioo
    (fun k x hx => realShiftedEdge_hasDerivAt a ha (hwithin x hx) k) hbound
    (show w∈Ioo (w-ε) (w+ε) by constructor <;> linarith) S.summable
    (show w∈Ioo (w-ε) (w+ε) by constructor <;> linarith)
  have hsumderiv : (∑'k,-2/(jacobi.Bessel.sigma a ha k+w)^2)= -(shiftedSecond a ha w)/2 := by
    calc
      _ = ∑'k,(-1/2:ℝ)*(realShiftedEdge a ha w k)^2 := by
        apply tsum_congr
        intro k
        unfold realShiftedEdge
        rw [div_pow]
        ring
      _ = (-1/2:ℝ)*(∑'k,(realShiftedEdge a ha w k)^2) := tsum_mul_left
      _ = _ := by rw [shiftedSecond]; ring
  rw [hsumderiv] at h
  exact h

/-- The printed off-edge second moment is exactly minus twice the derivative of the actual convergent original mass series.
Use: all shifted moment calibrations may use either of the source's two equivalent formulas for the same actual spectral data.
Article: jacobi, Appendix E.1.
Proof: the independently proved actual derivative determines the ordinary derivative; cancel the exact rational scalar. -/
theorem shiftedSecond_eq_deriv (a:ℝ) (ha:-1<a) {w:ℝ}
    (hw: - jacobi.Bessel.sigma a ha 0<w) :
    shiftedSecond a ha w= -2*deriv (shiftedMass a ha) w := by
  rw [(shiftedMass_hasDerivAt a ha hw).deriv]
  ring

end
end jacobi.EdgeResolvent

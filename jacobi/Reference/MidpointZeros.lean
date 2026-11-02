import jacobi.Reference.MidpointFormula
import jacobi.Reference.CharacteristicWeights
import jacobi.Reference.SpectralAnalytic

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual midpoint functions are rescaled reference characteristics.
Their complete complex zero sets are the original Dirichlet and Neumann
spectral classes. In particular there are no additional nonreal zeros.
The affine rescaling also proves energy analyticity without differentiating
the source square-root branch.
Use: cancels only a genuine nonzero normalization when identifying midpoint zeros and their simplicity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The exact common scalar in the actual midpoint formulas is strictly positive.
Use: cancels only a genuine nonzero normalization when identifying midpoint zeros and their simplicity.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: pi has a positive real power and gamma+1/2 is a positive Gamma argument. -/
theorem midpointScalar_pos {a : ℝ} (ha : -1<a) : 0<midpointScalar a :=
  mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by linarith [(parameters ha).1]))

/-- The original midpoint reference value is exactly a rescaled literal Gamma characteristic at every complex energy.
Use: proves its complete zero set and energy analyticity with the exact selected-branch normalization.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the reference exponent at order alpha/2+1/4 is (gamma+1)/2.
The frequency is halved while the energy is divided by four and shifted.
The proved true Gamma formula therefore gives the original characteristic. -/
theorem solution_midpoint_characteristic {a : ℝ} (ha : -1<a) (z : ℂ) :
    solution a z (1/2)=(midpointScalar a:ℂ)*
      characteristicTau (a/2+1/4)
        ((jacobi.Jacobi.endpointCorrection (a/2+1/4):ℂ)+
          (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/4) := by
  -- The exact square relation identifies the original characteristic independently of a chosen root branch.
  let omega := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hg : gamma (a/2+1/4)=(gamma a+1)/2 := by dsimp [gamma]; ring
  have hs : (omega/2)^2=
      ((jacobi.Jacobi.endpointCorrection (a/2+1/4):ℂ)+
        (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/4)-
          (jacobi.Jacobi.endpointCorrection (a/2+1/4):ℂ) := by
    rw [div_pow,frequency_square]
    ring
  rw [characteristicTau_eq _ hs]
  change wave a omega (1/2)=_
  rw [wave_midpoint_formula ha,characteristicGamma,hg]
  push_cast
  rw [show ((gamma a:ℂ)+1-omega/(Real.pi:ℂ))/2=
    ((gamma a:ℂ)+1)/2-(omega/2)/(Real.pi:ℂ) by ring,
    show ((gamma a:ℂ)+1+omega/(Real.pi:ℂ))/2=
      ((gamma a:ℂ)+1)/2+(omega/2)/(Real.pi:ℂ) by ring]
  ring

/-- The original actual spatial midpoint slope is exactly a rescaled literal Gamma characteristic at every complex energy.
Use: proves its full Neumann zero set and genuine entire energy dependence without a square-root derivative assumption.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the order alpha/2-3/4 has exponent gamma/2; halve the true frequency and apply the proved slope formula. -/
theorem solutionSlope_midpoint_characteristic {a : ℝ} (ha : -1<a) (z : ℂ) :
    solutionSlope a z (1/2)=(2*(Real.pi:ℂ)*(midpointScalar a:ℂ))*
      characteristicTau (a/2-3/4)
        ((jacobi.Jacobi.endpointCorrection (a/2-3/4):ℂ)+
          (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/4) := by
  -- Halving the genuine selected frequency gives the original reciprocal-Gamma slope factors exactly.
  let omega := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hg : gamma (a/2-3/4)=gamma a/2 := by dsimp [gamma]; ring
  have hs : (omega/2)^2=
      ((jacobi.Jacobi.endpointCorrection (a/2-3/4):ℂ)+
        (z-(jacobi.Jacobi.endpointCorrection a:ℂ))/4)-
          (jacobi.Jacobi.endpointCorrection (a/2-3/4):ℂ) := by
    rw [div_pow,frequency_square]
    ring
  rw [characteristicTau_eq _ hs]
  change waveSlope a omega (1/2)=_
  rw [waveSlope_midpoint_formula ha,characteristicGamma,hg]
  push_cast
  rw [show ((gamma a:ℂ)-omega/(Real.pi:ℂ))/2=
    (gamma a:ℂ)/2-(omega/2)/(Real.pi:ℂ) by ring,
    show ((gamma a:ℂ)+omega/(Real.pi:ℂ))/2=
      (gamma a:ℂ)/2+(omega/2)/(Real.pi:ℂ) by ring]
  ring

/-- Halving the reference exponent and energy gives exactly the corresponding every-other-index reference spectrum.
Use: identifies the actual complete midpoint zero sets in solution_midpoint_zero_iff and solutionSlope_midpoint_zero_iff.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: substitute the literal quadratic reference eigenvalues and the exact affine exponent relation. -/
theorem midpoint_spectrum_rescaling {a b : ℝ} (r k : ℕ)
    (hg : gamma b=(gamma a+r)/2) (z : ℂ) :
    (jacobi.Jacobi.endpointCorrection b:ℂ)+(z-(jacobi.Jacobi.endpointCorrection a:ℂ))/4=
      (eigenvalue b k:ℂ) ↔ z=(eigenvalue a (2*k+r):ℂ) := by
  unfold eigenvalue
  rw [hg]
  push_cast
  constructor <;> intro h
  · linear_combination 4*h
  · linear_combination h/4

/-- The actual reference midpoint value vanishes exactly at the original even one-based reference eigenvalues, with no other complex zeros.
Use: supplies the exhaustive Dirichlet midpoint class in Proposition C.2's reference comparison.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: cancel the proved positive original midpoint scalar, use the complete characteristic zero theorem and identify the exact rescaled spectrum. -/
theorem solution_midpoint_zero_iff {a : ℝ} (ha : -1<a) (z : ℂ) :
    solution a z (1/2)=0 ↔ ∃ k : ℕ,z=(eigenvalue a (2*k+1):ℂ) := by
  rw [solution_midpoint_characteristic ha,mul_eq_zero,
    or_iff_right (Complex.ofReal_ne_zero.mpr (midpointScalar_pos ha).ne'),characteristicTau_zero_iff]
  apply exists_congr
  intro k
  exact midpoint_spectrum_rescaling 1 k (by dsimp [gamma]; ring) z

/-- The actual reference midpoint slope vanishes exactly at the original odd one-based reference eigenvalues, with no other complex zeros.
Use: supplies the exhaustive Neumann midpoint class in Proposition C.2's reference comparison.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the original pi and midpoint normalizations are nonzero. The full characteristic zero theorem and exact affine spectral rescaling identify every zero. -/
theorem solutionSlope_midpoint_zero_iff {a : ℝ} (ha : -1<a) (z : ℂ) :
    solutionSlope a z (1/2)=0 ↔ ∃ k : ℕ,z=(eigenvalue a (2*k):ℂ) := by
  rw [solutionSlope_midpoint_characteristic ha,mul_eq_zero,
    or_iff_right (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (midpointScalar_pos ha).ne')),characteristicTau_zero_iff]
  apply exists_congr
  intro k
  simpa only [add_zero] using midpoint_spectrum_rescaling 0 k (by dsimp [gamma]; ring) z

/-- The actual spatial midpoint slope is an entire function of the original energy, including the frequency branch point.
Use: differentiates the genuine midpoint characteristic factorization and proves simple midpoint zeros.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: its exact rescaled characteristic formula is a constant times an entire function composed with a genuine affine energy map. -/
theorem solutionSlope_midpoint_analytic {a : ℝ} (ha : -1<a) (z : ℂ) :
    AnalyticAt ℂ (fun w => solutionSlope a w (1/2)) z := by
  have he : (fun w => solutionSlope a w (1/2))=(fun w =>
      (2*(Real.pi:ℂ)*(midpointScalar a:ℂ))*
        characteristicTau (a/2-3/4) ((jacobi.Jacobi.endpointCorrection (a/2-3/4):ℂ)+
          (w-(jacobi.Jacobi.endpointCorrection a:ℂ))/4)) :=
    funext (solutionSlope_midpoint_characteristic ha)
  rw [he]
  exact analyticAt_const.mul ((characteristicTau_analytic _ _).comp
    (analyticAt_const.add (analyticAt_id.sub analyticAt_const).div_const))

end
end jacobi.Reference

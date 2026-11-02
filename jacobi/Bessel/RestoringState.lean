import jacobi.Bessel.ScaledWave
import jacobi.Oscillation.PhaseRepresentation

/-!
Article: jacobi, Proposition B.1.
The original normalized entire Bessel wave instantiates the common genuine
restoring-solution interface. Nonvanishing of its two-dimensional state is
proved from the already established simplicity of its actual entire zeros.
Every interface input is discharged for the original function.
Use: proves the genuine positive Pruefer amplitude, rather than assuming nontriviality as an extra phase premise.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set MeasureTheory jacobi.Oscillation
set_option backward.isDefEq.respectTransparency false

/-- The actual original Bessel wave and its actual slope never vanish simultaneously on the positive axis.
Use: proves the genuine positive Pruefer amplitude, rather than assuming nontriviality as an extra phase premise.
Article: jacobi, Proposition B.1.
Proof: if the original wave vanishes, the original entire normalized
function vanishes at its squared argument. Its genuine spectral derivative
is nonzero by the proved simple-zero theorem. The explicit actual wave
slope reduces to a nonzero positive-power multiple of that derivative. -/
theorem wave_state_nonzero {a x : ℝ} (ha : -1<a) (hx : 0<x) :
    wave a x≠0 ∨ waveSlope a x≠0 := by
  -- The source's actual complex simple-zero theorem rules out a spurious zero state in this real phase construction.
  by_cases hz : wave a x=0
  · right
    have hF := (wave_zero_iff a hx).mp hz
    have hr : realNormalized a (x^2)=0 := (realNormalized_zero_iff a _).mpr hF
    rw [waveSlope,hr,mul_zero,zero_add]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Real.rpow_pos_of_pos hx _).ne') (realSlope_ne_zero ha hF)
  · exact Or.inl hz

/-- The actual original Bessel wave, with all genuine restoring-solution hypotheses discharged.
Use: constructs its continuous phase from the actual normalized-state integral and proves its true phase equation and original zero correspondence.
Article: jacobi, Proposition B.1.
-/
def restoringState (a : ℝ) (ha : -1<a) : RestoringSolution (Ioi (0:ℝ)) where
  value := wave a
  slope := waveSlope a
  potential := fun x => 1+(1/4-a^2)/x^2
  value_measurable := by
    have hF : Continuous (realNormalized a) := continuous_iff_continuousAt.mpr
      (fun x => (realNormalized_hasDerivAt a x).continuousAt)
    unfold wave
    fun_prop
  slope_measurable := by
    have hF : Continuous (realNormalized a) := continuous_iff_continuousAt.mpr
      (fun x => (realNormalized_hasDerivAt a x).continuousAt)
    have hG : Continuous (realSlope a) := continuous_iff_continuousAt.mpr
      (fun x => (realSlope_hasDerivAt a x).continuousAt)
    unfold waveSlope
    fun_prop
  potential_measurable := by fun_prop
  potential_continuous := by
    intro x hx
    have hxx : x^2≠0 := pow_ne_zero 2 (show 0<x from hx).ne'
    fun_prop (disch := exact hxx)
  first := fun x hx => wave_hasDerivAt a hx
  second := by
    intro x hx
    convert waveSlope_hasDerivAt a hx using 1
    nlinarith [wave_equation ha hx]
  nontrivial := fun x hx => wave_state_nonzero ha hx

/-- The actual Bessel phase density is exactly one plus its original inverse-square coefficient times the squared genuine normalized value coordinate.
Use: the correction is integrable at infinity and its literal oscillatory integral determines McMahon's remainder.
Article: jacobi, Proposition B.1.
Proof: specialize the proved exact normalized-state phase speed identity to the original restoring coefficient. -/
theorem restoringState_phaseDensity {a : ℝ} (ha : -1<a) {x : ℝ} (hx : 0<x) :
    (restoringState a ha).phaseDensity x=
      1+(1/4-a^2)/x^2*(restoringState a ha).unitSin x^2 := by
  rw [(restoringState a ha).phaseDensity_eq hx]
  congr 1
  dsimp [restoringState]
  ring

end
end jacobi.Bessel

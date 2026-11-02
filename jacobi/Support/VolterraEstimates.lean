import jacobi.Support.VolterraFirstDifference

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Both complete printed estimates hold together for the actual original
complex support wave, with one common pair of positive constants and
one common degree threshold on their original growing index ranges.
Use: the oscillatory transition argument and original complex edge limit use one actual uniform family of constants, with all original polynomial, recurrence, coupling and normalization premises discharged.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The full original support Volterra lemma holds with common genuine positive constants, including both complex wave errors and the adjacent-difference error.
Use: the oscillatory transition argument and original complex edge limit use one actual uniform family of constants, with all original polynomial, recurrence, coupling and normalization premises discharged.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the independently proved global cosh wave bound, reference-error bound and Wronskian first-difference bound concern the same genuine original support wave. Sum their positive constants and use monotonicity of the actual nonnegative cosh majorant to obtain one common pair on the full stated ranges. -/
theorem volterra_estimates {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,
      (∀m:ℕ,2*m≤n+6→∀y:ℂ,
        ‖naturalWave a b ha hb n m y‖≤C*((m:ℝ)+1)^gamma a*cosh (sqrt (B*volterraEnergy a b n m y)) ∧
        ‖naturalWave a b ha hb n m y-(topValue a b ha hb n m:ℂ)‖≤
          C*volterraEnergy a b n m y*((m:ℝ)+1)^gamma a*cosh (sqrt (B*volterraEnergy a b n m y))) ∧
      (∀m:ℕ,2*m≤n+4→∀y:ℂ,
        ‖(naturalWave a b ha hb n (m+1) y-naturalWave a b ha hb n m y)-
            ((topValue a b ha hb n (m+1):ℂ)-topValue a b ha hb n m)‖≤
          C*volterraEnergy a b n m y*((m:ℝ)+1)^(gamma a-1)*cosh (sqrt (B*volterraEnergy a b n m y))) := by
  -- Only the constants are combined here; every asserted bound has already been proved for the same actual original polynomial family.
  obtain ⟨C₁,B₁,hC₁,hB₁,hwave⟩ := naturalWave_cosh ha hb
  obtain ⟨C₂,B₂,hC₂,hB₂,herror⟩ := naturalWave_difference ha hb
  obtain ⟨C₃,B₃,hC₃,hB₃,hfirst⟩ := naturalWave_firstDifference ha hb
  let C := C₁+C₂+C₃
  let B := B₁+B₂+B₃
  have hC : 0<C := by dsimp [C]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  have hc₁ : C₁≤C := by dsimp [C]; linarith
  have hc₂ : C₂≤C := by dsimp [C]; linarith
  have hc₃ : C₃≤C := by dsimp [C]; linarith
  have hb₁ : B₁≤B := by dsimp [B]; linarith
  have hb₂ : B₂≤B := by dsimp [B]; linarith
  have hb₃ : B₃≤B := by dsimp [B]; linarith
  refine ⟨C,B,hC,hB,?_⟩
  filter_upwards [hwave,herror,hfirst] with n hw he hf
  constructor
  · intro m hm y
    have henergy : 0≤volterraEnergy a b n m y := by unfold volterraEnergy; positivity
    constructor
    · exact (hw m hm y).trans (mul_le_mul
        (mul_le_mul_of_nonneg_right hc₁ (by positivity))
        (volterra_cosh_mono a b n y hb₁ hB.le le_rfl) (cosh_pos _).le (by positivity))
    · exact (he m hm y).trans (mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₂ henergy) (by positivity))
        (volterra_cosh_mono a b n y hb₂ hB.le le_rfl) (cosh_pos _).le (by positivity))
  · intro m hm y
    have henergy : 0≤volterraEnergy a b n m y := by unfold volterraEnergy; positivity
    exact (hf m hm y).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc₃ henergy) (by positivity))
      (volterra_cosh_mono a b n y hb₃ hB.le le_rfl) (cosh_pos _).le (by positivity))

end
end jacobi.Support

import jacobi.Reference.HighFrequency
import jacobi.Reference.LowFrequency

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual reference wave has the minimum of its selected endpoint
scale and inverse-frequency scale, with precisely its true entire
exponential type. The endpoint-scale bound includes every complex
frequency, also zero, without an inverse-power totalization convention.
Use: combines with the inverse-frequency bound to give the original minimum envelope and with bounded frequencies to give the true global exponential type.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine original reference solution has a uniform endpoint-power bound with exactly its actual imaginary-frequency exponential at all large complex frequencies.
Use: combines with the inverse-frequency bound to give the original minimum envelope and with bounded frequencies to give the true global exponential type.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: before the true initial point use the actual selected small-scale
state bound. After it, the inverse frequency is at most 4*pi*t, so the
proved genuine high-frequency amplitude has the same endpoint-power
bound with a fixed coefficient. -/
theorem wave_endpoint_high_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*t^(gamma a)*Real.exp (t*|omega.im|) := by
  -- The actual energy propagation and the selected initial branch refer to the same source wave.
  obtain ⟨A,D,hA,_,hsmall⟩ := wave_small_scale ha
  obtain ⟨B,hB,hlarge⟩ := wave_uniform_high_frequency ha
  let C := A+B*(4*Real.pi)^(gamma a)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun omega homega t ht => ?_⟩
  have hR : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one homega
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  by_cases ht0 : t=0
  · subst t
    simp only [wave,(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htg := Real.rpow_pos_of_pos htp (gamma a)
  have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (by positivity)
  by_cases hstart : initialTime omega≤t
  · have hinit : 4*Real.pi*initialTime omega=‖omega‖⁻¹ := by
      dsimp [initialTime]
      field_simp [Real.pi_ne_zero,hR.ne']
    have hscale : ‖omega‖⁻¹≤4*Real.pi*t := by
      rw [← hinit]
      exact mul_le_mul_of_nonneg_left hstart (by positivity)
    have hp := Real.rpow_le_rpow (inv_nonneg.mpr hR.le) hscale hg.le
    rw [Real.mul_rpow (by positivity : 0≤4*Real.pi) htp.le] at hp
    rw [← Real.rpow_neg_eq_inv_rpow] at hp
    have hh := hlarge omega homega t ht
    calc
      _ ≤ B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) := hh
      _ ≤ B*((4*Real.pi)^(gamma a)*t^(gamma a))*Real.exp (t*|omega.im|) := by gcongr
      _ ≤ C*t^(gamma a)*Real.exp (t*|omega.im|) := by
        have hc : B*(4*Real.pi)^(gamma a)≤C := by dsimp [C]; linarith
        calc
          _ = (B*(4*Real.pi)^(gamma a))*t^(gamma a)*Real.exp (t*|omega.im|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc htg.le) (Real.exp_pos _).le
  · have hinit := initialTime_properties homega
    have hscale := mul_le_mul_of_nonneg_left (le_of_not_ge hstart) (show 0≤Real.pi*‖omega‖ by positivity)
    have hh := (hsmall omega homega t ⟨htp,ht.2⟩ (by nlinarith [hinit.2])).1
    calc
      _ ≤ A*t^(gamma a) := hh
      _ ≤ C*t^(gamma a) := mul_le_mul_of_nonneg_right
        (by dsimp [C]; exact le_add_of_nonneg_right (by positivity) : A≤C) htg.le
      _ ≤ C*t^(gamma a)*Real.exp (t*|omega.im|) := le_mul_of_one_le_right (by positivity) he

/-- The actual source reference wave has the full minimum endpoint/frequency envelope for every large complex frequency.
Use: supplies the genuine uniform source summand and transformed-profile bounds while preserving the exact entire exponential type.
Article: jacobi, Proposition 2.2.
Proof: use the two proved actual amplitude bounds and increase their
positive constants to one common sum. Choose the actual smaller of the
two endpoint and frequency scales. -/
theorem wave_minimum_high_frequency {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,1≤‖omega‖ → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*min (t^(gamma a)) (‖omega‖^(-gamma a))*Real.exp (t*|omega.im|) := by
  -- The smaller original scale is selected pointwise while both proven constants remain uniform.
  obtain ⟨A,hA,hendpoint⟩ := wave_endpoint_high_bound ha
  obtain ⟨B,hB,hfrequency⟩ := wave_uniform_high_frequency ha
  refine ⟨A+B,by positivity,fun omega homega t ht => ?_⟩
  have htgp := Real.rpow_nonneg ht.1 (gamma a)
  have hRp := Real.rpow_nonneg (norm_nonneg omega) (-gamma a)
  have hep := (Real.exp_pos (t*|omega.im|)).le
  by_cases h : t^(gamma a)≤‖omega‖^(-gamma a)
  · rw [min_eq_left h]
    exact (hendpoint omega homega t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : A≤A+B) htgp) hep)
  · rw [min_eq_right (le_of_not_ge h)]
    exact (hfrequency omega homega t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B≤A+B) hRp) hep)

/-- The genuine original reference solution has its selected endpoint scale and exact entire exponential type at every complex frequency, including zero.
Use: supplies the actual source growth hypothesis for the entire-function uniqueness argument in GL positivity.
Article: jacobi, Lemma C.1.
Proof: combine the genuine bounded-frequency series estimate with the
proved high-frequency endpoint estimate. The actual imaginary-frequency
exponential is at least one on the physical half interval. -/
theorem wave_global_endpoint_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*t^(gamma a)*Real.exp (t*|omega.im|) := by
  -- The bounded-frequency disk and its complement cover the true complex origin without an inverse-power convention there.
  obtain ⟨A,hA,hlow⟩ := wave_low_frequency ha
  obtain ⟨B,hB,hhigh⟩ := wave_endpoint_high_bound ha
  refine ⟨A+B,by positivity,fun omega t ht => ?_⟩
  have htgp := Real.rpow_nonneg ht.1 (gamma a)
  have hep := (Real.exp_pos (t*|omega.im|)).le
  by_cases h : 1≤‖omega‖
  · exact (hhigh omega h t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : B≤A+B) htgp) hep)
  · have hh := hlow omega (le_of_not_ge h) t ht
    have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (mul_nonneg ht.1 (abs_nonneg _))
    calc
      _ ≤ A*t^(gamma a) := hh
      _ ≤ (A+B)*t^(gamma a) := mul_le_mul_of_nonneg_right (by linarith : A≤A+B) htgp
      _ ≤ (A+B)*t^(gamma a)*Real.exp (t*|omega.im|) := le_mul_of_one_le_right
        (mul_nonneg (by positivity) htgp) he

end
end jacobi.Reference

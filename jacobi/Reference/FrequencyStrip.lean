import jacobi.Reference.EndpointFrequency

/-!
Article: jacobi, Proposition C.4.
The actual source minimum envelope holds at every nonzero complex
frequency in any prescribed horizontal strip, including bounded
frequencies. At zero frequency the separate endpoint envelope applies;
no totalized zero-to-a-negative-power is used to express infinity.
Use: supplies the actual uniform strip estimates for source characteristic contours, spectral profiles and the GL transformation.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology

/-- The genuine reference solution satisfies the exact source minimum amplitude bound on every fixed complex-frequency strip.
Use: supplies the actual uniform strip estimates for source characteristic contours, spectral profiles and the GL transformation.
Article: jacobi, Lemma C.1.
Proof: at large frequency apply the proved actual minimum envelope
and absorb its true exponential into exp(b/2). At bounded nonzero
frequency the inverse-frequency scale is at least one, so the selected
endpoint scale is the actual minimum; apply the genuine bounded-frequency
series estimate. The original zero frequency is covered separately by
the global endpoint theorem, since its printed inverse power is infinite. -/
theorem wave_strip_bound {a : ℝ} (ha : -1<a) (b : ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ omega:ℂ,omega≠0 → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*min (t^(gamma a)) (‖omega‖^(-gamma a)) := by
  -- Both ranges concern the identical actual wave, and the constants are uniform in the physical spatial endpoint.
  obtain ⟨A,hA,hhigh⟩ := wave_minimum_high_frequency ha
  obtain ⟨B,hB,hlow⟩ := wave_low_frequency ha
  let C := A*Real.exp (b/2)+B
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,fun omega hne him t ht => ?_⟩
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  have hmin : 0≤min (t^(gamma a)) (‖omega‖^(-gamma a)) :=
    le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hR : 1≤‖omega‖
  · have he : Real.exp (t*|omega.im|)≤Real.exp (b/2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul ht.2 him (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
      linarith
    calc
      _ ≤ A*min (t^(gamma a)) (‖omega‖^(-gamma a))*Real.exp (t*|omega.im|) := hhigh omega hR t ht
      _ ≤ A*min (t^(gamma a)) (‖omega‖^(-gamma a))*Real.exp (b/2) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hA.le hmin)
      _ = (A*Real.exp (b/2))*min (t^(gamma a)) (‖omega‖^(-gamma a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hmin
  · have hRp : 0<‖omega‖ := norm_pos_iff.mpr hne
    have hRle : ‖omega‖≤1 := (le_of_not_ge hR)
    have hrpow : 1≤‖omega‖^(-gamma a) := by
      have hh := Real.rpow_le_rpow_of_nonpos hRp hRle (neg_nonpos.mpr hg)
      simpa only [Real.one_rpow] using hh
    have htone : t^(gamma a)≤1 := Real.rpow_le_one ht.1 (by linarith [ht.2]) hg
    rw [min_eq_left (htone.trans hrpow)]
    exact (hlow omega hRle t ht).trans (mul_le_mul_of_nonneg_right
      (show B≤C by dsimp [C]; linarith [mul_pos hA (Real.exp_pos (b/2))]) (Real.rpow_nonneg ht.1 _))

end
end jacobi.Reference

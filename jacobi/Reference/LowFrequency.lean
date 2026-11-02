import jacobi.Reference.InitialScale

/-!
Article: jacobi, Proposition C.4.
A fixed genuine hypergeometric norm series controls the actual reference
core for |omega|<=1 and on the full physical half interval. The original
positive sine-power prefactor then gives the selected t^gamma amplitude
uniformly through omega=0, without using a totalized inverse power there.
Use: controls the genuine omega=0 region and completes the global entire-function growth estimate used in source GL injectivity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference core is uniformly bounded at bounded complex frequency and throughout a half-radius spatial disk.
Use: controls the genuine omega=0 region and completes the global entire-function growth estimate used in source GL injectivity.
Article: jacobi, Lemma C.1.
Proof: the two actual affine numerator norms are bounded by the same
fixed positive parameter. Their genuine 2F1 coefficients are dominated
by one true positive-parameter norm series at argument one half.
Bound the original sum by that genuinely summable series. -/
theorem waveCore_low_frequency (a : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,‖omega‖≤1 → ∀ x:ℂ,‖x‖≤1/2 → ‖waveCore a omega x‖≤C := by
  -- The coefficient comparison remains valid at the original zero frequency.
  let K := frequencyMajorant a
  have hK : 0<K := by dsimp [K,frequencyMajorant]; positivity
  let M := fun n => ‖ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) ((gamma a:ℂ)+1/2) n‖*(1/2:ℝ)^n
  have hM : Summable M := by
    have hh := Hypergeometric.summable_norm (u := (K:ℂ)) (v := (K:ℂ))
      (c := ((gamma a:ℂ)+1/2)) (x := (1/2:ℂ)) (by norm_num)
    convert hh using 1
    funext n
    dsimp only [M]
    rw [norm_mul (ordinaryHypergeometricCoefficient (K:ℂ) (K:ℂ) ((gamma a:ℂ)+1/2) n),norm_pow]
    norm_num
  refine ⟨(∑' n,M n)+1,by
    have hh : 0≤∑' n,M n := tsum_nonneg (fun n => by dsimp [M]; positivity)
    linarith,fun omega homega x hx => ?_⟩
  have hd : ‖omega/(Real.pi:ℂ)‖≤1/Real.pi := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right homega Real.pi_pos.le
  have hm : ‖(gamma a:ℂ)-omega/(Real.pi:ℂ)‖≤K := by
    have hh := norm_sub_le (gamma a:ℂ) (omega/(Real.pi:ℂ))
    rw [Complex.norm_real,Real.norm_eq_abs] at hh
    dsimp [K,frequencyMajorant]
    linarith
  have hp : ‖(gamma a:ℂ)+omega/(Real.pi:ℂ)‖≤K := by
    have hh := norm_add_le (gamma a:ℂ) (omega/(Real.pi:ℂ))
    rw [Complex.norm_real,Real.norm_eq_abs] at hh
    dsimp [K,frequencyMajorant]
    linarith
  have ht (n : ℕ) : ‖frequencyCoefficient a n omega*x^n‖≤M n := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul (Hypergeometric.coefficient_norm_le hK hm hp n)
      (pow_le_pow_left₀ (norm_nonneg _) hx n) (by positivity) (norm_nonneg _)
  have hs : Summable (fun n => ‖frequencyCoefficient a n omega*x^n‖) :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) ht
  have he : waveCore a omega x=∑' n,frequencyCoefficient a n omega*x^n := by
    rw [waveCore,ordinaryHypergeometric_eq_tsum]
    rfl
  rw [he]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ht hM).trans (by linarith))

/-- The genuine original cosine coordinate stays inside the closed half-radius spatial disk on the full physical half interval.
Use: applies the actual bounded-frequency hypergeometric series estimate all the way to the source midpoint.
Article: jacobi, Proposition C.4.
Proof: the actual half-interval cosine is nonnegative, and the genuine shifted cosine coordinate is nonnegative. -/
theorem coordinate_half_bound {t : ℝ} (ht : t∈Icc 0 (1/2)) : ‖(coordinate t:ℂ)‖≤1/2 := by
  have hc : 0≤Real.cos (Real.pi*t) := Real.cos_nonneg_of_mem_Icc
    ⟨by nlinarith [Real.pi_pos,ht.1],by nlinarith [Real.pi_pos,ht.2]⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coordinate_properties.2.2 t).1]
  dsimp [coordinate]
  linarith

/-- The actual selected reference solution has a uniform endpoint-power amplitude at every bounded complex frequency, including zero.
Use: completes the true entire-frequency growth estimate on the source half interval.
Article: jacobi, Lemma C.1.
Proof: multiply the true bounded core estimate at the actual half-interval coordinate by the genuine prefactor bound; handle the original zero spatial endpoint directly. -/
theorem wave_low_frequency {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega:ℂ,‖omega‖≤1 → ∀ t∈Icc (0:ℝ) (1/2),
      ‖wave a omega t‖≤C*t^(gamma a) := by
  -- The selected positive endpoint power handles the actual spatial endpoint separately from the bounded interior core.
  obtain ⟨C,hC,hbound⟩ := waveCore_low_frequency a
  refine ⟨C,hC,fun omega homega t ht => ?_⟩
  by_cases ht0 : t=0
  · subst t
    simp only [wave,(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  · have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hti : t∈Ioo 0 1 := ⟨htp,by linarith [ht.2]⟩
    rw [wave,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos a hti)]
    exact (mul_le_mul (weight_half_bound ha ⟨htp,ht.2⟩)
      (hbound omega homega (coordinate t:ℂ) (coordinate_half_bound ht)) (norm_nonneg _)
      (Real.rpow_pos_of_pos htp (gamma a)).le).trans_eq (by ring)

end
end jacobi.Reference

import jacobi.Analytic.ReferenceSharpFrequency
import jacobi.Reference.SharpDerivativeLow

/-!
Article: jacobi, Lemma C.1.
Spatially scaled energy circles cover the low-frequency-spatial regime,
including the branch point. Together with the uniform frequency Cauchy
estimate this proves the exact printed energy derivative bound for
complex orders, with constants uniform on every compact order set.
Use: applies the actual endpoint envelope on Cauchy circles even when their shifted centre is complex.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] solution wave

/-- The genuine square-root frequency on a spatially scaled complex energy disk has uniformly bounded scaled norm.
Use: applies the actual endpoint envelope on Cauchy circles even when their shifted centre is complex.
Article: jacobi, Lemma C.1.
Proof: the exact square identity bounds t squared times the shifted energy norm by two; its nonnegative square root is consequently at most two. -/
theorem scaled_complex_energy_disk {t:ℝ} (ht:0<t) {omega z c:ℂ}
    (hscale:‖omega‖*t≤1) (hz:‖z-(c+omega^2)‖≤1/t^2) :
    t*‖Complex.sqrt (z-c)‖≤2 := by
  -- The only square-root fact used is its true algebraic square identity.
  let v := Complex.sqrt (z-c)
  have hs : ‖v‖^2=‖z-c‖ := by rw [← norm_pow,jacobi.Reference.frequency_square]
  have hn : ‖z-c‖≤1/t^2+‖omega‖^2 := by
    calc
      _ = ‖(z-(c+omega^2))+omega^2‖ := by congr 1; ring
      _ ≤ ‖z-(c+omega^2)‖+‖omega^2‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_pow]; exact add_le_add hz le_rfl
  have hh := mul_le_mul_of_nonneg_left (hs.trans_le hn) (sq_nonneg t)
  have hid : t^2*(1/t^2+‖omega‖^2)=1+(‖omega‖*t)^2 := by field_simp
  rw [hid] at hh
  have hsq := (sq_le_sq₀ (mul_nonneg (norm_nonneg omega) ht.le) zero_le_one).mpr hscale
  change t*‖v‖≤2
  nlinarith [mul_nonneg ht.le (norm_nonneg v)]

/-- The original complex-order energy derivative has the exact small-scale spatial gain, with uniform order constants.
Use: proves the low-scale branch of the printed fboundC(b) derivative estimate.
Article: jacobi, Lemma C.1.
Proof: the actual energy function is entire. On its radius 1/t squared Cauchy circle the scaled square-root frequency is at most two. The genuine global endpoint envelope has only the fixed exponential exp(2); division by the radius gives precisely the two extra powers of t. -/
theorem sharp_energy_deriv_low_uniform {G δ:ℝ} (hG:0<G) (hδ:0<δ) :
    ∃ C:ℝ,0<C ∧ ∀ a omega:ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → ∀ t∈Ioc (0:ℝ) (1/2),‖omega‖*t≤1 →
        ‖deriv (fun z => solution a z t) (jacobi.Hankel.besselCoefficient a+omega^2)‖≤C*t^(gamma a).re*t^2 := by
  -- The energy circle does not require a holomorphic choice of frequency square root.
  obtain ⟨A,hA,hamp⟩ := wave_global_endpoint_uniform hG hδ
  refine ⟨A*Real.exp 2,by positivity,fun a omega hag ha hc t ht hscale => ?_⟩
  have hr : 0<1/t^2 := one_div_pos.mpr (sq_pos_of_pos ht.1)
  have hcircle (z:ℂ) (hz:z∈sphere (jacobi.Hankel.besselCoefficient a+omega^2) (1/t^2)) :
      ‖solution a z t‖≤A*Real.exp 2*t^(gamma a).re := by
    have hz' : ‖z-(jacobi.Hankel.besselCoefficient a+omega^2)‖≤1/t^2 :=
      le_of_eq (by simpa only [mem_sphere,dist_eq_norm] using hz)
    let v := Complex.sqrt (z- jacobi.Hankel.besselCoefficient a)
    have hscaled := scaled_complex_energy_disk ht.1 hscale hz'
    have him : t*|v.im|≤2 :=
      (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm v) ht.1.le).trans hscaled
    have hh := hamp a v hag ha hc t ⟨ht.1.le,ht.2⟩
    rw [← solution_eq_wave a (jacobi.Reference.frequency_square _) t] at hh
    calc
      _ ≤ A*t^(gamma a).re*Real.exp (t*|v.im|) := hh
      _ ≤ A*t^(gamma a).re*Real.exp 2 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr him) (mul_nonneg hA.le (Real.rpow_nonneg ht.1.le _))
      _ = _ := by ring
  have hd : DifferentiableOn ℂ (fun z => solution a z t) univ := fun z _ =>
    (solution_energy_analytic hag ⟨ht.1.le,by linarith [ht.2]⟩ z).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  exact (Complex.norm_cderiv_le hr hcircle).trans_eq (by field_simp)

/-- The actual reference solution satisfies the full printed sharp energy derivative bound uniformly over bounded admissible complex orders.
Use: closes the missing derivative assertion of fboundC(b), beyond the weaker estimate sufficient for the GL series.
Article: jacobi, Lemma C.1.
Proof: below t*abs(omega)=1 the small-scale energy bound is stronger than the printed estimate and the minimum is the endpoint power. Above that threshold the minimum is the reciprocal-frequency power, and the exact chain rule converts the scaled frequency Cauchy bound. The zero spatial endpoint is identically zero in energy. -/
theorem sharp_energy_derivative_uniform {G δ:ℝ} (hG:0<G) (hδ:0<δ) (b:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ a omega:ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → 1≤‖omega‖ → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
        ‖deriv (fun z => solution a z t) (jacobi.Hankel.besselCoefficient a+omega^2)‖≤
          C*t/‖omega‖*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) := by
  -- The two genuine Cauchy scales meet at the exact threshold of the source minimum.
  obtain ⟨A,hA,hlow⟩ := sharp_energy_deriv_low_uniform hG hδ
  obtain ⟨B,hB,hhigh⟩ := sharp_wave_deriv_uniform hG hδ b
  refine ⟨A+B,by positivity,fun a omega hag ha hc hR him t ht => ?_⟩
  have hRp : 0<‖omega‖ := zero_lt_one.trans_le hR
  have hg : 0≤(gamma a).re := hag.le
  by_cases ht0 : t=0
  · subst t
    have hz : (fun z:ℂ => solution a z 0)=fun _ => (0:ℂ) := by
      funext z
      have hne : gamma a≠0 := ne_of_apply_ne Complex.re hag.ne'
      simp only [solution,weight,mul_zero,Real.sin_zero,zero_div,Complex.ofReal_zero,Complex.zero_cpow hne,zero_mul]
    simp only [hz,deriv_const,norm_zero,mul_zero,zero_div,zero_mul,le_refl]
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases hscale : ‖omega‖*t≤1
  · have htR : t≤‖omega‖⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hRp).mpr (by nlinarith)
    have hmin : t^(gamma a).re≤‖omega‖^(-(gamma a).re) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow ht.1 htR hg
    rw [min_eq_left hmin]
    have ht2 : t^2≤t/‖omega‖ := (le_div_iff₀ hRp).mpr (by nlinarith)
    calc
      _ ≤ A*t^(gamma a).re*t^2 := hlow a omega hag ha hc t ⟨htp,ht.2⟩ hscale
      _ ≤ A*t^(gamma a).re*(t/‖omega‖) := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ ≤ (A+B)*t/‖omega‖*t^(gamma a).re := by
        have hh := mul_le_mul_of_nonneg_right (show A≤A+B by linarith)
          (mul_nonneg (Real.rpow_nonneg ht.1 (gamma a).re) (div_nonneg ht.1 hRp.le))
        convert hh using 1 <;> ring
  · have hscale' : 1≤‖omega‖*t := le_of_not_ge hscale
    have htR : ‖omega‖⁻¹≤t := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hRp).mpr (by nlinarith)
    have hmin : ‖omega‖^(-(gamma a).re)≤t^(gamma a).re := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow (inv_nonneg.mpr hRp.le) htR hg
    rw [min_eq_right hmin]
    have hh := hhigh a omega hag ha hc him t ⟨htp,ht.2⟩ hscale'
    rw [wave_energy_derivative_uniform hag ht omega,norm_mul,norm_mul] at hh
    norm_num only [Complex.norm_ofNat] at hh
    have hb := mul_le_mul_of_nonneg_right (show B≤A+B by linarith)
      (mul_nonneg ht.1 (Real.rpow_nonneg hRp.le (-(gamma a).re)))
    have he : (A+B)*t/‖omega‖*‖omega‖^(-(gamma a).re)=
        ((A+B)*t*‖omega‖^(-(gamma a).re))/‖omega‖ := by ring
    rw [he]
    apply (le_div_iff₀ hRp).mpr
    nlinarith [mul_nonneg (norm_nonneg (deriv (fun z => solution a z t)
      (jacobi.Hankel.besselCoefficient a+omega^2))) (norm_nonneg omega)]

end
end jacobi.ComplexReference

import jacobi.Reference.SharpEnergyDerivative

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Energy Cauchy circles of radius 1/t^2 stay in a bounded scaled-frequency
disk whenever t*|omega|<=1. This includes z=c_0 and yields the sharp
energy derivative at the singular spatial endpoint without choosing a
differentiable square-root branch.
Use: bounds the genuine exponential type on the low-scale Cauchy circles in sharp_energy_deriv_low.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution wave

/-- The actual square-root frequency on a spatially scaled energy disk has scaled norm at most two.
Use: bounds the genuine exponential type on the low-scale Cauchy circles in sharp_energy_deriv_low.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the square of the frequency norm is the norm of the shifted
energy. The triangle inequality bounds its product with t^2 by two;
the nonnegative scaled norm is therefore at most two. -/
theorem scaled_energy_disk {a t : ℝ} (ht : 0<t) {omega z : ℂ}
    (hscale : ‖omega‖*t≤1)
    (hz : ‖z-((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤1/t^2) :
    t*‖Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))‖≤2 := by
  -- Only the true square identity is used, so the energy disk may cross the branch cut.
  let v := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hs : ‖v‖^2=‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖ := by
    rw [← norm_pow,frequency_square]
  have hn : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖≤1/t^2+‖omega‖^2 := by
    calc
      _ = ‖(z-((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2))+omega^2‖ := by congr 1; ring
      _ ≤ ‖z-((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖+‖omega^2‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_pow]; exact add_le_add hz le_rfl
  have hh := mul_le_mul_of_nonneg_left (hs.trans_le hn) (sq_nonneg t)
  have hid : t^2*(1/t^2+‖omega‖^2)=1+(‖omega‖*t)^2 := by field_simp
  rw [hid] at hh
  have hsq := (sq_le_sq₀ (mul_nonneg (norm_nonneg omega) ht.le) zero_le_one).mpr hscale
  change t*‖v‖≤2
  nlinarith [mul_nonneg ht.le (norm_nonneg v)]

/-- The genuine reference energy derivative is bounded by C*t^(gamma+2) throughout the small spatial-frequency region.
Use: completes the low-scale half of sharp_energy_derivative, with no hypothesis on the energy branch point.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: on the energy circle of radius 1/t^2 the actual scaled frequency
norm is at most two. The global endpoint envelope therefore has the
fixed exponential factor exp(2). Cauchy's derivative estimate divides
by this genuine radius, giving exactly two additional powers of t. -/
theorem sharp_energy_deriv_low {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,∀ t∈Ioc (0:ℝ) (1/2),‖omega‖*t≤1 →
      ‖deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
        C*t^(gamma a)*t^2 := by
  -- The argument uses entire energy dependence, rather than differentiating a chosen square root.
  obtain ⟨A,hA,hamp⟩ := wave_global_endpoint_bound ha
  refine ⟨A*Real.exp 2,by positivity,fun omega t ht hscale => ?_⟩
  have hr : 0<1/t^2 := one_div_pos.mpr (sq_pos_of_pos ht.1)
  have hcircle (z : ℂ)
      (hz : z∈Metric.sphere ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) (1/t^2)) :
      ‖solution a z t‖≤A*Real.exp 2*t^(gamma a) := by
    have hz' : ‖z-((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤1/t^2 := by
      exact le_of_eq (by simpa only [Metric.mem_sphere,dist_eq_norm] using hz)
    let v := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
    have hscaled := scaled_energy_disk ht.1 hscale hz'
    have him : t*|v.im|≤2 :=
      (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm v) ht.1.le).trans hscaled
    have hh := hamp v t ⟨ht.1.le,ht.2⟩
    rw [← solution_eq_wave a (frequency_square _) t] at hh
    calc
      _ ≤ A*t^(gamma a)*Real.exp (t*|v.im|) := hh
      _ ≤ A*t^(gamma a)*Real.exp 2 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr him) (mul_nonneg hA.le (Real.rpow_nonneg ht.1.le _))
      _ = _ := by ring
  have hd : DifferentiableOn ℂ (fun z => solution a z t) univ := fun z _ =>
    (solution_energy_analytic_half ha ⟨ht.1.le,ht.2⟩ z).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  exact (Complex.norm_cderiv_le hr hcircle).trans_eq (by field_simp)

/-- The actual reference solution satisfies the full printed sharp energy derivative estimate on every horizontal frequency strip.
Use: supplies the source's refined spectral and contour estimates and differentiability bounds for the GL transformation.
Article: jacobi, Lemma C.1.
Proof: below t*|omega|=1 the minimum is t^gamma, and the energy Cauchy
estimate C*t^(gamma+2) is stronger than the stated bound. Above that
threshold the minimum is |omega|^(-gamma); use the scaled frequency
Cauchy estimate and the exact chain rule. At t=0 the actual solution
is identically zero as a function of energy. -/
theorem sharp_energy_derivative {a : ℝ} (ha : -1<a) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,1≤‖omega‖ → |omega.im|≤b →
      ∀ t∈Icc (0:ℝ) (1/2),
        ‖deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
          C*t/‖omega‖*min (t^(gamma a)) (‖omega‖^(-gamma a)) := by
  -- The two Cauchy scales meet at the exact threshold of the printed minimum.
  obtain ⟨A,hA,hlow⟩ := sharp_energy_deriv_low ha
  obtain ⟨B,hB,hhigh⟩ := sharp_wave_deriv_high ha b
  refine ⟨A+B,by positivity,fun omega hR him t ht => ?_⟩
  have hRp : 0<‖omega‖ := lt_of_lt_of_le zero_lt_one hR
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  by_cases ht0 : t=0
  · subst t
    have hz : (fun z : ℂ => solution a z 0)=(fun _ => (0:ℂ)) := funext (solution_zero ha)
    simp only [hz,deriv_const,norm_zero,mul_zero,zero_div,zero_mul,le_refl]
  have htp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  by_cases hscale : ‖omega‖*t≤1
  · have htR : t≤‖omega‖⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hRp).mpr (by nlinarith)
    have hmin : t^(gamma a)≤‖omega‖^(-gamma a) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow ht.1 htR hg
    rw [min_eq_left hmin]
    have ht2 : t^2≤t/‖omega‖ := (le_div_iff₀ hRp).mpr (by nlinarith)
    calc
      _ ≤ A*t^(gamma a)*t^2 := hlow omega t ⟨htp,ht.2⟩ hscale
      _ ≤ A*t^(gamma a)*(t/‖omega‖) := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ ≤ (A+B)*t/‖omega‖*t^(gamma a) := by
        have hh := mul_le_mul_of_nonneg_right (show A≤A+B by linarith)
          (mul_nonneg (Real.rpow_nonneg ht.1 (gamma a)) (div_nonneg ht.1 hRp.le))
        convert hh using 1 <;> ring
  · have hscale' : 1≤‖omega‖*t := (le_of_not_ge hscale)
    have htR : ‖omega‖⁻¹≤t := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hRp).mpr (by nlinarith)
    have hmin : ‖omega‖^(-gamma a)≤t^(gamma a) := by
      rw [Real.rpow_neg_eq_inv_rpow]
      exact Real.rpow_le_rpow (inv_nonneg.mpr hRp.le) htR hg
    rw [min_eq_right hmin]
    have hh := hhigh omega him t ⟨htp,ht.2⟩ hscale'
    rw [wave_energy_derivative ha ht omega,norm_mul,norm_mul] at hh
    norm_num only [Complex.norm_ofNat] at hh
    have hD : 0≤‖deriv (fun z => solution a z t)
        ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖*‖omega‖ := by positivity
    have hb := mul_le_mul_of_nonneg_right (show B≤A+B by linarith)
      (mul_nonneg ht.1 (Real.rpow_nonneg hRp.le (-gamma a)))
    have he : (A+B)*t/‖omega‖*‖omega‖^(-gamma a)=
        ((A+B)*t*‖omega‖^(-gamma a))/‖omega‖ := by ring
    rw [he]
    apply (le_div_iff₀ hRp).mpr
    nlinarith

end
end jacobi.Reference

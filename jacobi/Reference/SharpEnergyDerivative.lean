import jacobi.Reference.FrequencyStrip
import jacobi.Reference.SolutionBounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The Cauchy radius must follow the spatial scale. For |omega|*t >= 1,
use a frequency circle of radius 1/(2*t), then differentiate z=c_0+omega^2.
For |omega|*t <= 1, an energy circle of radius t^(-2) also covers the
frequency branch point. Both arguments apply to the actual reference f.
Source: Cauchy's derivative estimate, mathlib Complex.norm_cderiv_le.
Use: converts the spatially scaled frequency Cauchy estimate into the sharp energy bound below.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution wave

/-- The genuine energy derivative and frequency derivative are related by the exact chain rule, including the spatial endpoint.
Use: converts the spatially scaled frequency Cauchy estimate into the sharp energy bound below.
Article: jacobi, Lemma C.1.
Proof: compose the actual entire energy solution with c_0+omega^2 and use its proved independence of the chosen square root. -/
theorem wave_energy_derivative {a : ℝ} (ha : -1<a) {t : ℝ}
    (ht : t∈Icc 0 (1/2)) (omega : ℂ) :
    deriv (fun w => wave a w t) omega=
      deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)*(2*omega) := by
  -- The polynomial energy parametrization has no branch point in its own frequency variable.
  have he : (fun w : ℂ => solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) t)=
      (fun w => wave a w t) := funext fun w => solution_eq_wave a (by ring) t
  have hp : HasDerivAt (fun w : ℂ => (jacobi.Jacobi.endpointCorrection a:ℂ)+w^2)
      (2*omega) omega := by
    convert ((hasDerivAt_id omega).pow 2).const_add
      (jacobi.Jacobi.endpointCorrection a:ℂ) using 1 <;> norm_num
  have hf : HasDerivAt (fun z : ℂ => solution a z t)
      (deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2))
      ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) :=
    (solution_energy_analytic_half ha ht
      ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)).differentiableAt.hasDerivAt
  have hd := HasDerivAt.comp (h₂ := fun z : ℂ => solution a z t)
    (h := fun w : ℂ => (jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) omega hf hp
  change HasDerivAt
    (fun w : ℂ => solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) t)
    (deriv (fun z => solution a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)*
      (2*omega)) omega at hd
  rw [he] at hd
  exact hd.deriv

/-- A frequency circle of radius 1/(2*t) retains at least half the central frequency when |omega|*t>=1, and increases the scaled imaginary part by at most one half.
Use: controls the actual reference amplitude on the precise Cauchy circles in sharp_wave_deriv_high.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the direct and reverse triangle inequalities control the norm, and the imaginary part is bounded by the same true distance. -/
theorem frequency_cauchy_circle {t : ℝ} (ht : 0<t) {omega v : ℂ}
    (hscale : 1≤‖omega‖*t) (hv : ‖v-omega‖≤1/(2*t)) :
    ‖omega‖/2≤‖v‖ ∧ t*|v.im|≤t*|omega.im|+1/2 := by
  -- The radius is no larger than half the central frequency in this region.
  have hr : 1/(2*t)≤‖omega‖/2 := (div_le_iff₀ (by positivity : 0<2*t)).mpr (by nlinarith)
  have hn := norm_sub_norm_le omega v
  rw [norm_sub_rev omega v] at hn
  have him : |v.im|≤|omega.im|+‖v-omega‖ := by
    have hh := abs_add_le omega.im (v.im-omega.im)
    have he := Complex.abs_im_le_norm (v-omega)
    simp only [sub_im] at he
    rw [add_sub_cancel] at hh
    linarith
  refine ⟨by linarith,?_⟩
  have hh := mul_le_mul_of_nonneg_left (him.trans
    (add_le_add le_rfl hv)) ht.le
  have hid : t*(|omega.im|+1/(2*t))=t*|omega.im|+1/2 := by field_simp
  rw [hid] at hh
  linarith

/-- The actual frequency derivative gains the full factor t above the spatial frequency threshold.
Use: supplies the high-frequency half of the exact printed energy derivative estimate.
Article: jacobi, Lemma C.1.
Proof: apply Cauchy's estimate on the genuine frequency circle of radius
1/(2*t). Its frequencies remain at least |omega|/2>=1, and its exact
imaginary exponential is bounded independently of omega and t in the
prescribed strip. The positive source exponent controls the inverse power. -/
theorem sharp_wave_deriv_high {a : ℝ} (ha : -1<a) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,|omega.im|≤b → ∀ t∈Ioc (0:ℝ) (1/2),
      1≤‖omega‖*t → ‖deriv (fun w => wave a w t) omega‖≤C*t*‖omega‖^(-gamma a) := by
  -- Cauchy's radius follows t, so the derivative retains the printed spatial gain.
  obtain ⟨A,hA,hamp⟩ := wave_uniform_high_frequency ha
  let D := A*(2:ℝ)^(gamma a)*Real.exp (b/2+1/2)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨2*D,by positivity,fun omega him t ht hscale => ?_⟩
  have hR : 2≤‖omega‖ := by nlinarith [norm_nonneg omega,ht.2]
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  have hcircle (v : ℂ) (hv : v∈Metric.sphere omega (1/(2*t))) :
      ‖wave a v t‖≤D*‖omega‖^(-gamma a) := by
    have hv' : ‖v-omega‖≤1/(2*t) := by
      exact le_of_eq (by simpa only [Metric.mem_sphere,dist_eq_norm] using hv)
    obtain ⟨hn,hi⟩ := frequency_cauchy_circle ht.1 hscale hv'
    have hpow : ‖v‖^(-gamma a)≤(2:ℝ)^(gamma a)*‖omega‖^(-gamma a) := by
      have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0<‖omega‖/2) hn (neg_nonpos.mpr hg)
      rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul] at hh
      simpa only [mul_comm] using hh
    have hExp : Real.exp (t*|v.im|)≤Real.exp (b/2+1/2) := by
      apply Real.exp_le_exp.mpr
      have hb : 0≤b := (abs_nonneg omega.im).trans him
      have hh := mul_le_mul ht.2 him (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
      linarith
    calc
      _ ≤ A*‖v‖^(-gamma a)*Real.exp (t*|v.im|) := hamp v (by linarith) t ⟨ht.1.le,ht.2⟩
      _ ≤ A*((2:ℝ)^(gamma a)*‖omega‖^(-gamma a))*Real.exp (b/2+1/2) := by gcongr
      _ = _ := by dsimp [D]; ring
  have hd : DifferentiableOn ℂ (fun w => wave a w t) univ := fun w _ =>
    (wave_frequency_analytic a ⟨ht.1,by linarith [ht.2]⟩ w).differentiableAt.differentiableWithinAt
  have hr : 0<1/(2*t) := one_div_pos.mpr (mul_pos (by norm_num) ht.1)
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  have hh := Complex.norm_cderiv_le hr hcircle
  exact hh.trans_eq (by field_simp)

end
end jacobi.Reference

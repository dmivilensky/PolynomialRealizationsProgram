import jacobi.Analytic.ReferenceEnergyAnalytic
import jacobi.Analytic.ReferenceStripBounds
import jacobi.Reference.SharpEnergyDerivative

/-!
Article: jacobi, Lemma C.1.
The spatially scaled Cauchy argument for real order is transferred to
the genuine complex-order wave with constants uniform in the order.
The radius 1/(2*t) retains the exact additional spatial factor t.
Use: controls the spatially scaled energy Cauchy circles in the sharp low-scale derivative estimate.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local irreducible] solution wave

/-- The actual complex-order reference wave has its endpoint-power envelope at every complex frequency, with common order constants.
Use: controls the spatially scaled energy Cauchy circles in the sharp low-scale derivative estimate.
Article: jacobi, Lemma C.1.
Proof: combine the proved uniform high-frequency endpoint estimate with the bounded-frequency estimate; the genuine exponential factor is at least one. -/
theorem wave_global_endpoint_uniform {G δ : ℝ} (hG : 0<G) (hδ : 0<δ) :
    ∃ C:ℝ,0<C ∧ ∀ a omega:ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → ∀ t∈Icc (0:ℝ) (1/2),
        ‖wave a omega t‖≤C*t^(gamma a).re*Real.exp (t*|omega.im|) := by
  -- Both frequency regions use the same actual reference function and endpoint normalization.
  obtain ⟨A,hA,hhigh⟩ := wave_endpoint_high_bound hG hδ
  obtain ⟨B,hB,hlow⟩ := wave_low_frequency hG hδ
  refine ⟨A+B,by positivity,fun a omega hag ha hc t ht => ?_⟩
  have hp : 0≤t^(gamma a).re := Real.rpow_nonneg ht.1 _
  have he : 1≤Real.exp (t*|omega.im|) := Real.one_le_exp (mul_nonneg ht.1 (abs_nonneg _))
  by_cases hR : 1≤‖omega‖
  · exact (hhigh a omega hag ha hc hR t ht).trans (by gcongr; linarith)
  · have hh := hlow a omega hag ha hc (le_of_not_ge hR) t ht
    have hm := mul_le_mul_of_nonneg_left he (mul_nonneg hB.le hp)
    exact hh.trans (by nlinarith [mul_nonneg hA.le hp,Real.exp_pos (t*|omega.im|)])

/-- The original complex-order energy and frequency derivatives obey the exact chain rule.
Use: converts the scaled frequency Cauchy bound into the printed sharp energy derivative bound.
Article: jacobi, Lemma C.1.
Proof: the actual energy function is entire, even at the frequency branch point. Compose it with the genuine polynomial energy parametrization and use the proved frequency-square identity. -/
theorem wave_energy_derivative_uniform {a:ℂ} (ha:0<(gamma a).re) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (1/2)) (omega:ℂ) :
    deriv (fun w => wave a w t) omega=
      deriv (fun z => solution a z t) (jacobi.Hankel.besselCoefficient a+omega^2)*(2*omega) := by
  -- The energy parametrization is polynomial; no differentiable square root is chosen.
  have he : (fun w:ℂ => solution a (jacobi.Hankel.besselCoefficient a+w^2) t)=
      (fun w => wave a w t) := funext (fun w => solution_eq_wave a (by ring) t)
  have hp : HasDerivAt (fun w:ℂ => jacobi.Hankel.besselCoefficient a+w^2) (2*omega) omega := by
    convert ((hasDerivAt_id omega).pow 2).const_add (jacobi.Hankel.besselCoefficient a) using 1 <;> norm_num
  have hf := (solution_energy_analytic ha ⟨ht.1,by linarith [ht.2]⟩
    (jacobi.Hankel.besselCoefficient a+omega^2)).differentiableAt.hasDerivAt
  have hd := HasDerivAt.comp (h₂ := fun z:ℂ => solution a z t)
    (h := fun w:ℂ => jacobi.Hankel.besselCoefficient a+w^2) omega hf hp
  change HasDerivAt (fun w:ℂ => solution a (jacobi.Hankel.besselCoefficient a+w^2) t) _ omega at hd
  rw [he] at hd
  exact hd.deriv

/-- The frequency derivative has the full spatial gain uniformly over bounded admissible complex orders on every fixed frequency strip.
Use: proves the high-scale branch of the printed complex energy derivative estimate.
Article: jacobi, Lemma C.1.
Proof: use a frequency circle of radius 1/(2*t). The previously proved geometric lemma gives half the central frequency and a bounded scaled imaginary part on that circle. Bound its actual amplitude uniformly in order and apply the scalar Cauchy derivative estimate. -/
theorem sharp_wave_deriv_uniform {G δ:ℝ} (hG:0<G) (hδ:0<δ) (b:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ a omega:ℂ,0<(gamma a).re → ‖gamma a‖≤G →
      δ≤(gamma a+1/2).re → |omega.im|≤b → ∀ t∈Ioc (0:ℝ) (1/2),
      1≤‖omega‖*t → ‖deriv (fun w => wave a w t) omega‖≤C*t*‖omega‖^(-(gamma a).re) := by
  -- The common coefficient 2^G controls the varying exponent on the same scaled Cauchy circle.
  obtain ⟨A,hA,hamp⟩ := wave_uniform_high_frequency hG hδ
  let D : ℝ := A*(2:ℝ)^G*Real.exp (b/2+1/2)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨2*D,by positivity,fun a omega hag ha hc him t ht hscale => ?_⟩
  have hR : 2≤‖omega‖ := by nlinarith [norm_nonneg omega,ht.2]
  have hcircle (v:ℂ) (hv:v∈sphere omega (1/(2*t))) :
      ‖wave a v t‖≤D*‖omega‖^(-(gamma a).re) := by
    have hv' : ‖v-omega‖≤1/(2*t) := le_of_eq
      (by simpa only [mem_sphere,dist_eq_norm] using hv)
    obtain ⟨hn,hi⟩ := jacobi.Reference.frequency_cauchy_circle ht.1 hscale hv'
    have hpow : ‖v‖^(-(gamma a).re)≤(2:ℝ)^G*‖omega‖^(-(gamma a).re) := by
      have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0<‖omega‖/2) hn (by linarith : -(gamma a).re≤0)
      rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul] at hh
      have hg : (gamma a).re≤G := (Complex.re_le_norm _).trans ha
      have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hg
      exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg omega) (-(gamma a).re))])
    have hExp : Real.exp (t*|v.im|)≤Real.exp (b/2+1/2) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul ht.2 him (abs_nonneg _) (by norm_num : (0:ℝ)≤1/2)
      linarith
    calc
      _ ≤ A*‖v‖^(-(gamma a).re)*Real.exp (t*|v.im|) := hamp a v hag ha hc (by linarith) t ⟨ht.1.le,ht.2⟩
      _ ≤ A*((2:ℝ)^G*‖omega‖^(-(gamma a).re))*Real.exp (b/2+1/2) := by gcongr
      _ = _ := by dsimp [D]; ring
  have hd : DifferentiableOn ℂ (fun w => wave a w t) univ := fun w _ =>
    (wave_comp_analytic analyticAt_const analyticAt_id hag ⟨ht.1.le,by linarith [ht.2]⟩).differentiableAt.differentiableWithinAt
  have hr : 0<1/(2*t) := one_div_pos.mpr (mul_pos (by norm_num) ht.1)
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd hr (subset_univ _)]
  exact (Complex.norm_cderiv_le hr hcircle).trans_eq (by field_simp)

end
end jacobi.ComplexReference

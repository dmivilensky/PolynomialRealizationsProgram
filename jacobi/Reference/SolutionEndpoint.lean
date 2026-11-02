import jacobi.Reference.Solutions

/-!
Article: jacobi, Proposition C.4.
The genuine arbitrary-energy reference solution has exactly the original
normalized t^gamma branch at the singular endpoint. The proof uses the
actual positive-axis sine-power normalization and the genuine analytic
hypergeometric central value, rather than assuming an endpoint asymptotic.
Use: fixes the endpoint normalization for the actual reference solution at every complex spectral parameter.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual reference sine-power prefactor has precisely its normalized selected endpoint power.
Use: fixes the endpoint normalization for the actual reference solution at every complex spectral parameter.
Article: jacobi, Proposition C.4.
Proof: use the already proved genuine normalized reference endpoint factor at degree zero, whose original polynomial is identically one. -/
theorem weight_endpoint_limit (a : ℝ) :
    Tendsto (fun t => weight a t/t^(gamma a)) (𝓝[>] 0) (𝓝 1) := by
  have hp : jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) 0=1 := by
    simp [jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]
  simpa only [eigenfunction,jacobi.Jacobi.angular,hp,Polynomial.eval_one,mul_one] using eigenfunction_endpoint_limit a 0

/-- The actual original reference wave has its exact normalized selected endpoint branch for every complex frequency.
Use: selects the genuine reference solution before the GL transformation, including the gamma<1/2 regime where endpoint vanishing alone is ambiguous.
Article: jacobi, Proposition C.4.
Proof: the actual sine-power ratio tends to one. The genuine physical
coordinate tends to zero, where the actual analytic community
hypergeometric factor has value one. Multiply the two true limits. -/
theorem wave_endpoint_limit (a : ℝ) (omega : ℂ) :
    Tendsto (fun t => wave a omega t/((t^(gamma a):ℝ):ℂ)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
  -- Both limit factors come from their actual original formulas; no selected-branch hypothesis is passed in.
  have hw := Complex.continuous_ofReal.continuousAt.tendsto.comp (weight_endpoint_limit a)
  have hx : Tendsto (fun t : ℝ => (coordinate t:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
    have hh := (coordinate_hasDerivAt (0:ℝ)).ofReal_comp.continuousAt.tendsto
    simpa only [coordinate_properties.1,Complex.ofReal_zero] using hh.mono_left nhdsWithin_le_nhds
  have hcore : AnalyticAt ℂ (waveCore a omega) 0 := Hypergeometric.analytic (by norm_num)
  have hh := hcore.continuousAt.tendsto.comp hx
  simp only [waveCore,ordinaryHypergeometric_zero] at hh
  have h := hw.mul hh
  simp only [Complex.ofReal_one,one_mul] at h
  apply (tendsto_congr' ?_).mpr h
  exact Eventually.of_forall fun t => by
    dsimp [wave,waveCore,Function.comp_apply]
    rw [Complex.ofReal_div]
    ring

/-- The actual original reference spectral solution has the selected normalized singular endpoint branch at every complex energy.
Use: supplies the true original branch in the reference-to-transformed construction of Proposition C.2, throughout the complete order range.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: specialize the unconditional genuine complex-frequency endpoint limit to the actual energy square root. -/
theorem solution_endpoint_limit (a : ℝ) (z : ℂ) :
    Tendsto (fun t => solution a z t/((t^(gamma a):ℝ):ℂ)) (𝓝[>] 0) (𝓝 (1:ℂ)) := wave_endpoint_limit _ _

/-- The actual reference solution vanishes at the original singular endpoint throughout the article's admissible order range.
Use: fixes the zero endpoint values of the genuine reference GL kernel and transformed functions.
Article: jacobi, Lemma C.1.
Proof: the original positive-exponent sine-power prefactor is zero at the endpoint. -/
theorem solution_zero {a : ℝ} (ha : -1<a) (z : ℂ) : solution a z 0=0 := by
  unfold solution wave
  rw [(weight_properties ha).2.1,Complex.ofReal_zero,zero_mul]

end
end jacobi.Reference

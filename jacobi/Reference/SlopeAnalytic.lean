import jacobi.Reference.WaveAnalytic
import jacobi.Reference.HypergeometricDerivative
import jacobi.Complex.EvenDescent

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The genuine spatial slope of the original reference solution is entire
in frequency and energy at every physical interior point. The proof
uses the actual hypergeometric derivative and even descent, including
the energy branch point, so subsequent Cauchy estimates concern true
derivatives of the same slope used in the differential equation.
Use: waveSlope_frequency_analytic proves actual frequency analyticity of the source spatial slope without assuming a mixed-derivative identity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine spatial derivative of the original hypergeometric core is the shifted original core with its exact coefficient.
Use: waveSlope_frequency_analytic proves actual frequency analyticity of the source spatial slope without assuming a mixed-derivative identity.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Source: Gauss's differentiation formula, DLMF 15.5.1, proved here in HypergeometricDerivative.
Proof: shifting both numerator parameters and the denominator by one
is exactly the original core with gamma replaced by gamma+1, hence alpha replaced by alpha+2. -/
theorem waveCore_derivative_shift {a : ℝ} (ha : -1<a) (omega : ℂ) {x : ℂ} (hx : ‖x‖<1) :
    deriv (waveCore a omega) x=
      (((gamma a:ℂ)-omega/(Real.pi:ℂ))*((gamma a:ℂ)+omega/(Real.pi:ℂ))/((gamma a:ℂ)+1/2))*
        waveCore (a+2) omega x := by
  have hc : 0<((gamma a:ℂ)+1/2).re := by
    norm_num
    linarith [(parameters ha).1]
  have hg : gamma (a+2)=gamma a+1 := by dsimp [gamma]; ring
  rw [waveCore,Hypergeometric.derivative_shift hc hx,waveCore,hg]
  push_cast
  congr 2 <;> ring

/-- The actual original spatial slope is entire in its complex frequency.
Use: solutionSlope_energy_analytic and slope Cauchy estimates establish the actual mixed spectral-spatial bound needed to differentiate F.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: express the true core derivative by its proved shifted core.
Both original core families are entire in frequency and their exact
coefficient is polynomial in frequency divided by a fixed scalar. -/
theorem waveSlope_frequency_analytic {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) (omega : ℂ) :
    AnalyticAt ℂ (fun w => waveSlope a w t) omega := by
  -- All analytic factors are actual source cores evaluated at the genuine interior coordinate.
  have hx := coordinate_norm_lt_one ht
  have he : (fun w => waveSlope a w t)=(fun w:ℂ => (weight a t:ℂ)*
      ((weightLogSlope a t:ℂ)*waveCore a w (coordinate t:ℂ)+
        (coordinateSlope t:ℂ)*((((gamma a:ℂ)-w/(Real.pi:ℂ))*
          ((gamma a:ℂ)+w/(Real.pi:ℂ))/((gamma a:ℂ)+1/2))*waveCore (a+2) w (coordinate t:ℂ)))) := by
    funext w
    rw [waveSlope,waveCore_derivative_shift ha w hx]
  rw [he]
  have hq : AnalyticAt ℂ (fun w:ℂ =>
      (((gamma a:ℂ)-w/(Real.pi:ℂ))*((gamma a:ℂ)+w/(Real.pi:ℂ))/((gamma a:ℂ)+1/2))) omega :=
    ((analyticAt_const.sub analyticAt_id.div_const).mul
      (analyticAt_const.add analyticAt_id.div_const)).div_const
  exact analyticAt_const.mul ((analyticAt_const.mul (waveCore_frequency_analytic a hx omega)).add
    (analyticAt_const.mul (hq.mul (waveCore_frequency_analytic (a+2) hx omega))))

/-- The genuine original spatial slope is even in frequency at every physical interior point.
Use: solutionSlope_energy_analytic removes the apparent square-root singularity in the actual energy slope.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the actual waves agree at opposite frequencies as spatial
functions. Their independently proved genuine spatial derivatives must agree. -/
theorem waveSlope_even (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    waveSlope a (-omega) t=waveSlope a omega t := by
  have he : wave a (-omega)=wave a omega := funext (wave_even a omega)
  have hd := wave_hasDerivAt a (-omega) ht
  rw [he] at hd
  exact hd.unique (wave_hasDerivAt a omega ht)

/-- The original spatial slope is entire in its genuine complex energy, including the original frequency branch point.
Use: the true energy Cauchy derivative of partial_t f controls spatial derivatives of the GL summand differences in Appendix C.2 (c).
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the actual frequency slope is entire and even, so the proved
even-entire descent applies to the same square-root expression defining
solutionSlope. Compose with the original constant energy shift. -/
theorem solutionSlope_energy_analytic {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) (z : ℂ) :
    AnalyticAt ℂ (fun w => solutionSlope a w t) z := by
  exact (jacobi.Complex.even_entire_descent (waveSlope_frequency_analytic ha ht)
    (fun w => waveSlope_even a w ht) (z-(jacobi.Jacobi.endpointCorrection a:ℂ))).comp
      (f := fun w:ℂ => w-(jacobi.Jacobi.endpointCorrection a:ℂ))
      (analyticAt_id.sub analyticAt_const)

/-- Any complex frequency with the prescribed energy gives the identical actual spatial reference slope.
Use: waveSlope_energy_derivative applies the genuine polynomial frequency chain rule without differentiating a square-root branch.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the two frequency roots have the same square, and the actual source slope is even. -/
theorem solutionSlope_eq_wave (a : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) {z omega : ℂ}
    (hz : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) :
    solutionSlope a z t=waveSlope a omega t := by
  exact jacobi.Complex.even_eq_of_square_eq (f := fun w => waveSlope a w t)
    (fun w => waveSlope_even a w ht)
    ((frequency_square _).trans hz.symm)

/-- The actual frequency derivative of the original spatial slope is exactly twice the frequency times its genuine energy derivative.
Use: the original mixed spectral-spatial estimate follows from the true frequency Cauchy estimate and this exact chain rule.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: compose the proved entire actual energy slope with the
polynomial original energy c_0+omega^2. The proved root-independent
slope identity identifies this composition with the actual frequency slope. -/
theorem waveSlope_energy_derivative {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) (omega : ℂ) :
    deriv (fun w => waveSlope a w t) omega=
      deriv (fun z => solutionSlope a z t) ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)*(2*omega) := by
  -- Both derivatives are those of the same source spatial slope, including at the energy branch point.
  have he : (fun w:ℂ => solutionSlope a ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) t)=
      (fun w => waveSlope a w t) := funext (fun w => solutionSlope_eq_wave a ht (by ring))
  have hp : HasDerivAt (fun w:ℂ => (jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) (2*omega) omega := by
    convert! ((hasDerivAt_id omega).pow 2).const_add (jacobi.Jacobi.endpointCorrection a:ℂ) using 1
    norm_num
  have h := ((solutionSlope_energy_analytic ha ht _).differentiableAt.hasDerivAt).comp omega hp
  change HasDerivAt (fun w:ℂ => solutionSlope a ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) t) _ omega at h
  rw [he] at h
  exact h.deriv

end
end jacobi.Reference

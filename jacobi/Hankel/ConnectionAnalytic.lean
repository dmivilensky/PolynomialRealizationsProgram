import jacobi.Hankel.SlopeAnalytic
import jacobi.Hankel.BesselDecomposition

/-!
Article: jacobi, Lemma E.1.
Use: complexBesselWaveSlope_analytic supplies genuine analytic Bessel Cauchy data in the original Jost connection formula.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter jacobi.Bessel
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual original normalized Bessel spectral derivative is holomorphic in complex order on its original admissible half-plane.
Use: complexBesselWaveSlope_analytic supplies genuine analytic Bessel Cauchy data in the original Jost connection formula.
Article: jacobi, Lemma E.1.
Proof: on the actual open half-plane use the proved genuine adjacent-order derivative identity F_alpha'=-F_(alpha+1)/(4*(alpha+1)). Both original factors are analytic and their true affine denominator is nonzero. -/
theorem normalized_slope_order_analytic {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    AnalyticAt ℂ (fun b : ℂ => deriv (normalized b) z) a := by
  -- The actual spectral derivative is identified by its proved adjacent-order identity, not by a presumed interchange of derivatives.
  have ha1 : -1<(a+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hn : 4*(a+1)≠(0:ℂ) := mul_ne_zero (by norm_num)
    (by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).1)
  have hF := ((normalized_order_holomorphic z).analyticAt (order_halfPlane_open.mem_nhds ha1)).comp
    (f := fun b : ℂ => b+1) (analyticAt_id.add analyticAt_const)
  have hc : AnalyticAt ℂ (fun b : ℂ => (-1:ℂ)/(4*(b+1))) a := by fun_prop
  apply (hc.mul hF).congr
  filter_upwards [order_halfPlane_open.mem_nhds ha] with b hb
  exact (normalized_derivative_order_shift hb z).symm

/-- The actual original complex-order Bessel Liouville value is holomorphic in order at every fixed spatial point.
Use: the original outgoing and incoming connection coefficients have actual analytic Bessel values in their fixed-base Cauchy formulas.
Article: jacobi, Lemma E.1.
Proof: multiply the original entire exponential order factor by the actual normalized Bessel function, already proved holomorphic in its order half-plane. -/
theorem complexBesselWave_analytic {a : ℂ} (ha : -1<a.re) (x : ℝ) :
    AnalyticAt ℂ (fun b : ℂ => complexBesselWave b x) a := by
  have hF := (normalized_order_holomorphic ((x:ℂ)^2)).analyticAt (order_halfPlane_open.mem_nhds ha)
  have hP : AnalyticAt ℂ (fun b : ℂ => complexWaveFactor b x) a := by unfold complexWaveFactor; fun_prop
  exact hP.mul hF

/-- The actual original complex-order Bessel Liouville spatial slope is holomorphic in order at every fixed spatial point.
Use: outgoingBesselCoefficient_analytic and incomingBesselCoefficient_analytic have both genuine Bessel Cauchy data analytic on their actual common order domain.
Article: jacobi, Lemma E.1.
Proof: use the actual exponential prefactor, the original normalized Bessel order analyticity and the proved adjacent-order analytic formula for its genuine spectral derivative. -/
theorem complexBesselWaveSlope_analytic {a : ℂ} (ha : -1<a.re) (x : ℝ) :
    AnalyticAt ℂ (fun b : ℂ => complexBesselWaveSlope b x) a := by
  have hF := (normalized_order_holomorphic ((x:ℂ)^2)).analyticAt (order_halfPlane_open.mem_nhds ha)
  have hG := normalized_slope_order_analytic ha ((x:ℂ)^2)
  have hP : AnalyticAt ℂ (fun b : ℂ => complexWaveFactor b x) a := by unfold complexWaveFactor; fun_prop
  exact hP.mul (((analyticAt_id.add (analyticAt_const (v := (1/2:ℂ)))).div_const (c := (x:ℂ))).mul hF |>.add
    ((analyticAt_const (v := 2*(x:ℂ))).mul hG))

/-- The genuine fixed-base outgoing coefficient of the original Bessel-Jost decomposition is holomorphic on its actual admissible complex-order contraction domain.
Use: the complex identity theorem extends the independently proved true real numbered-zero connection phase to one common complex-order disk.
Article: jacobi, Lemma E.1.
Proof: its original Cauchy formula at R+1 combines the true analytic Bessel value and slope, the actual incoming Banach amplitude evaluation, and the proved analytic Fourier slope. Its only denominator is the genuine nonzero Jost value -2i. -/
theorem outgoingBesselCoefficient_analytic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) :
    AnalyticAt ℂ (outgoingBesselCoefficient hR) a := by
  -- All Cauchy data are evaluated at one original point common to the whole order neighborhood.
  have hx : R≤R+1 := by linarith
  have hY := complexBesselWave_analytic ha (R+1)
  have hY' := complexBesselWaveSlope_analytic ha (R+1)
  have hm := ((BoundedContinuousFunction.evalCLM ℂ (R+1) : OutgoingSpace →L[ℂ] ℂ).analyticAt _).comp
    (incomingAmplitude_analytic hR hc)
  have hm' := incomingAmplitudeSlope_analytic hR hx hc
  exact ((analyticAt_const (v := realPhase (-Complex.I) (R+1))).mul
    (((hY.mul hm').sub (hY'.mul hm)).sub (((analyticAt_const (v := Complex.I)).mul hY).mul hm))).div_const
      (c := -2*Complex.I)

/-- The genuine fixed-base incoming coefficient of the original Bessel-Jost decomposition is holomorphic on the same actual complex-order domain.
Use: the exact complex-order relative phase follows from these actual analytic coefficients and the proved original real numbered-zero phase.
Article: jacobi, Lemma E.1.
Proof: apply ordinary analytic algebra to the original fixed-base Cauchy formula, using the genuine analytic Bessel Cauchy data and both actual outgoing amplitude and slope. -/
theorem incomingBesselCoefficient_analytic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : -1<a.re) (hc : ‖besselCoefficient a‖/R<1) :
    AnalyticAt ℂ (incomingBesselCoefficient hR) a := by
  -- The same fixed spatial point is used for the original incoming and outgoing coefficients.
  have hx : R≤R+1 := by linarith
  have hY := complexBesselWave_analytic ha (R+1)
  have hY' := complexBesselWaveSlope_analytic ha (R+1)
  have hp := ((BoundedContinuousFunction.evalCLM ℂ (R+1) : OutgoingSpace →L[ℂ] ℂ).analyticAt _).comp
    (besselAmplitude_analytic hR hc)
  have hp' := besselAmplitudeSlope_analytic hR hx hc
  exact ((analyticAt_const (v := realPhase Complex.I (R+1))).mul
    (((hY'.mul hp).sub (hY.mul hp')).sub (((analyticAt_const (v := Complex.I)).mul hY).mul hp))).div_const
      (c := -2*Complex.I)

end
end jacobi.Hankel

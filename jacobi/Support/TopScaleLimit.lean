import jacobi.Support.TopProfile

/-!
Article: jacobi, Appendix C.3 (polynomial and derivative envelopes).
The genuine first sine factor of the original top-node product has
its exact moving-mesh limit with the original nonintegral frequency
and actual degree normalization. The printed endpoint constant is
computed before combining the three original sine products.
Use: topScale_limit computes both genuine sine arguments with the correct original mesh normalization.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The original support step times the actual degree tends to pi, also with the exact n+1 matrix-dimension convention of the spectral polynomials.
Use: topScale_limit computes both genuine sine arguments with the correct original mesh normalization.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the original Darboux step identity expresses the n+1 dimension step as the n dimension step with alpha shifted by two. The already proved actual frequency-to-degree ratio tends to one. -/
theorem support_step_limit (a b : ℝ) {ι : Type*} {l : Filter ι} {n : ι→ℕ}
    (hn:Tendsto n l atTop) :
    Tendsto (fun i => (n i:ℝ)*step a b (n i+1)) l (𝓝 π) := by
  have h := (((jacobi.Jacobi.frequency_ratio_tendsto (a+2) b).comp hn).inv₀ one_ne_zero).const_mul π
  simp only [inv_one,mul_one] at h
  convert h using 1
  funext i
  rw [← step_darboux]
  simp only [Function.comp_def,step,inv_div]
  ring

/-- The actual original support step tends to zero along every cofinal degree sequence.
Use: topScale_limit evaluates the genuine normalized denominator sine by continuity of sinc at zero.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: its original frequency diverges, and the exact step is pi divided by that frequency. -/
theorem support_step_zero (a b : ℝ) {ι : Type*} {l : Filter ι} {n : ι→ℕ}
    (hn:Tendsto n l atTop) : Tendsto (fun i => step a b (n i+1)) l (𝓝 (0:ℝ)) :=
  ((jacobi.Jacobi.frequency_tendsto a b).comp ((tendsto_add_atTop_nat 1).comp hn)).const_div_atTop π

/-- The genuine sine has its exact continuous sinc normalization at every real argument, including zero.
Use: topScale_limit computes the original degree-normalized boundary sine without division by a vanishing angle.
Article: jacobi, Appendix C.3 (top-node polynomials).
Source: the definition of Real.sinc and its continuous zero extension.
Proof: at zero both sides vanish; otherwise substitute the actual sinc quotient and cancel its same nonzero argument. -/
theorem sin_eq_mul_sinc (x : ℝ) : sin x=x*sinc x := by
  by_cases hx:x=0
  · simp [hx]
  · rw [sinc_of_ne_zero hx,mul_div_cancel₀ _ hx]

/-- The actual first top-node sine-product factor has precisely the printed normalized limit along every original moving mesh index.
Use: topValue_limit combines this genuine scalar limit with the three actual sine-product limits to identify the full exact original U profile.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: the original numerator angle tends to pi*t and the true step times degree tends to pi. The denominator n*sin(bar_gamma*h) tends to pi*bar_gamma through its exact continuous sinc factorization. Divide by this genuine nonzero original constant. -/
theorem topScale_limit {a b : ℝ} (ha:-1<a) (hb:-1<b) {ι : Type*} {l : Filter ι} {n m : ι→ℕ}
    {t : ℝ} (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => (sin (((m i:ℝ)+averageGamma a b)*step a b (n i+1))/
      sin (averageGamma a b*step a b (n i+1)))/(n i:ℝ)) l
      (𝓝 (sin (π*t)/(π*averageGamma a b))) := by
  -- The genuine boundary sine is normalized separately, preserving the original positive bar_gamma factor.
  have hg := parameter_pos ha hb
  have hstep := support_step_limit a b hn
  have hsmall : Tendsto (fun i => averageGamma a b/(n i:ℝ)) l (𝓝 (0:ℝ)) :=
    (tendsto_natCast_atTop_atTop.comp hn).const_div_atTop (averageGamma a b)
  have hangle : Tendsto (fun i => ((m i:ℝ)+averageGamma a b)*step a b (n i+1)) l (𝓝 (π*t)) := by
    have h := (hm.add hsmall).mul hstep
    simp only [add_zero] at h
    rw [mul_comm t π] at h
    apply (tendsto_congr' ?_).mpr h
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℕ))] with i hi
    have hni : (n i:ℝ)≠0 := by exact_mod_cast hi.ne'
    field_simp [hni]
  have hzero := (support_step_zero a b hn).const_mul (averageGamma a b)
  simp only [mul_zero] at hzero
  have hsinc := continuous_sinc.continuousAt.tendsto.comp hzero
  simp only [sinc_zero,Function.comp_def] at hsinc
  have hden : Tendsto (fun i => (n i:ℝ)*sin (averageGamma a b*step a b (n i+1))) l
      (𝓝 (π*averageGamma a b)) := by
    have h := (hstep.mul_const (averageGamma a b)).mul hsinc
    simp only [mul_one] at h
    convert h using 1
    funext i
    rw [sin_eq_mul_sinc]
    ring
  have h := (continuous_sin.continuousAt.tendsto.comp hangle).div hden (mul_pos pi_pos hg.2.2).ne'
  convert h using 1
  funext i
  simp only [Pi.div_apply,Function.comp_def]
  ring

end
end jacobi.Support

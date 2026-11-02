import jacobi.Reference.Eigenfunctions

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
Every actual reference Gegenbauer function is t^gamma times an even
analytic factor equal to one at zero. This proves the actual selected
branch, rather than merely vanishing at the singular endpoint. In
particular it distinguishes the required branch when gamma<1/2.
Use: identifies its selected t^gamma branch and its vanishing endpoint Wronskians.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine regular factor of the original reference eigenfunction at the singular left endpoint.
Use: identifies its selected t^gamma branch and its vanishing endpoint Wronskians.
Article: jacobi, Proposition C.4.
-/
def regularFactor (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (Real.sinc (Real.pi*t))^(gamma a)* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)

/-- The actual reference regular factor is even on the whole real axis.
Use: its first derivative vanishes at zero, supplying the extra endpoint order in Green's identity.
Article: jacobi, Proposition C.4.
Proof: sinc and cosine are even, as is the polynomial in cosine. -/
theorem regularFactor_even (a : ℝ) (k : ℕ) (t : ℝ) : regularFactor a k (-t)=regularFactor a k t := by
  simp only [regularFactor,mul_neg,Real.sinc_neg,jacobi.Jacobi.angular,Real.cos_neg]

/-- Every actual reference regular factor is genuinely analytic at the singular endpoint.
Use: proves the full selected branch even when endpoint vanishing alone would admit two solutions.
Article: jacobi, Proposition C.4.
Proof: sinc(pi*t) is analytic and equals one at zero. Its fixed real power is analytic there by the proved positive-power lemma; multiply by the original analytic angular polynomial. -/
theorem regularFactor_analytic (a : ℝ) (k : ℕ) : AnalyticAt ℝ (regularFactor a k) 0 := by
  have hi : AnalyticAt ℝ (fun t : ℝ => Real.pi*t) 0 := analyticAt_const.mul analyticAt_id
  have hs := (jacobi.Jacobi.sinc_analytic (Real.pi*0)).comp (f := fun t : ℝ => Real.pi*t) hi
  exact (jacobi.Jacobi.analytic_positive_rpow hs (by norm_num) (gamma a)).mul
    ((jacobi.Jacobi.angular_analytic (jacobiIndex a) (jacobiIndex a) k (Real.pi*0)).comp
      (f := fun t : ℝ => Real.pi*t) hi)

/-- The actual reference regular factor has exactly the source's normalization one.
Use: rules out the zero solution and fixes the original reference norming constants.
Article: jacobi, Lemma C.1.
Proof: sinc(0)=1 and the actual normalized Jacobi endpoint value is one. -/
theorem regularFactor_zero (a : ℝ) (k : ℕ) : regularFactor a k 0=1 := by
  simp only [regularFactor,mul_zero,Real.sinc_zero,Real.one_rpow,one_mul,
    jacobi.Jacobi.angular,Real.cos_zero,sub_self,zero_div,jacobi.Jacobi.shiftedPolynomial_zero]

/-- The actual selected reference branch has an even regular factor with zero central derivative.
Use: proves the original endpoint Green terms vanish, including throughout gamma<1/2.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: apply the existing genuine derivative parity theorem to the actual even analytic factor. -/
theorem regularFactor_deriv_zero (a : ℝ) (k : ℕ) : deriv (regularFactor a k) 0=0 :=
  jacobi.Jacobi.even_derivative_zero (regularFactor_analytic a k).differentiableAt (regularFactor_even a k)

/-- The original reference Gegenbauer function has precisely the selected regular-singular factorization at every positive interior point.
Use: supplies the real source branch and endpoint normalization for the reference spectral realization and GL transformation.
Article: jacobi, Proposition C.4.
Proof: sin(pi*t)/pi=t*sinc(pi*t). The two positive interior factors permit the genuine real-power product rule. -/
theorem eigenfunction_factor (a : ℝ) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    eigenfunction a k t=t^(gamma a)*regularFactor a k t := by
  -- The regular factor is actually defined at zero and analytic there; this is more information than endpoint vanishing.
  have ht0 : Real.pi*t≠0 := mul_ne_zero Real.pi_ne_zero ht.1.ne'
  have hs : 0<Real.sinc (Real.pi*t) := by
    rw [Real.sinc_of_ne_zero ht0]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1) (by nlinarith [Real.pi_pos,ht.2])) (mul_pos Real.pi_pos ht.1)
  have hid : sin (Real.pi*t)/Real.pi=t*Real.sinc (Real.pi*t) := by
    rw [Real.sinc_of_ne_zero ht0]
    field_simp [Real.pi_ne_zero,ht.1.ne']
  unfold eigenfunction weight regularFactor
  rw [hid,Real.mul_rpow ht.1.le hs.le]
  ring

/-- The actual reference eigenfunction has the exact required normalized endpoint limit.
Use: selects the source reference solution rather than an arbitrary vanishing solution at a limit-circle endpoint.
Article: jacobi, Lemma C.1.
Proof: cancel the nonzero positive endpoint power in the actual factorization; its genuine regular factor is continuous and equals one at zero. -/
theorem eigenfunction_endpoint_limit (a : ℝ) (k : ℕ) :
    Tendsto (fun t => eigenfunction a k t/t^(gamma a)) (𝓝[>] 0) (𝓝 1) := by
  -- The limit is for the actual normalized original functions, not an independent solution with an assumed asymptotic.
  have h : Tendsto (regularFactor a k) (𝓝[>] 0) (𝓝 (regularFactor a k 0)) :=
    (regularFactor_analytic a k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [regularFactor_zero] at h
  apply (tendsto_congr' ?_).mpr h
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0,t<1 :=
    (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ))≤𝓝 0) (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [self_mem_nhdsWithin,hupper] with t ht ht1
  rw [eigenfunction_factor a k ⟨ht,ht1⟩]
  exact mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos ht _).ne'

end
end jacobi.Reference

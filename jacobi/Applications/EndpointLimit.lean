import jacobi.Applications.EndpointCovarianceBounds

/-!
Article: jacobi, Theorem 5.1.
The original Nesterov realization has the printed cubic endpoint constant
for every b>-1. The quantitative proof uses the actual causal impulse
energy, with all approximation premises discharged by finite recurrences.
Use: Article checks the source endpoint lemma directly, including b=0.
-/
namespace jacobi.Applications
noncomputable section
open Filter chebyshev1
open scoped Topology

/-- The genuine original endpoint squared gain has exactly the source's general-momentum cubic limit.
Use: Article checks the complete endpoint lemma for the actual Nesterov realization, independently of any numerical certificate.
Article: jacobi, Lemma A.2.
Proof: the actual energy differs from its explicit cubic particular solution by at most M*k^2. Divide by k^3. The remainder and the lower-degree polynomial terms tend to zero, leaving the exact cubic coefficient. -/
theorem endpoint_gain_limit {b:ℝ} (hb:-1<b) :
    Tendsto (fun k:ℕ=>((nesterovMethod b).kernelNorm k 0 0)^2/(k:ℝ)^3)
      atTop (𝓝 (2/(3*(b+3)*(2*b+3)))) := by
  -- Both the error estimate and the gain identification concern the original two-memory method.
  obtain ⟨M,_,hM⟩:=endpointCovariance_bounds hb
  have hi:Tendsto (fun k:ℕ=>(k:ℝ)⁻¹) atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr:Tendsto (fun k:ℕ=>(endpointEnergy b k-endpointEPoly b k)/(k:ℝ)^3)
      atTop (𝓝 0):=by
    apply squeeze_zero_norm' ?_ (tendsto_natCast_atTop_atTop.const_div_atTop M)
    filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
    have hkp:(0:ℝ)<k:=by exact_mod_cast (show 0<k by omega)
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (pow_nonneg hkp.le _)]
    calc
      _≤(M*(k:ℝ)^2)/(k:ℝ)^3:=div_le_div_of_nonneg_right (hM k hk).2.2 (pow_nonneg hkp.le _)
      _=M/(k:ℝ):=by field_simp
  have hp:Tendsto (fun k:ℕ=>endpointEPoly b k/(k:ℝ)^3)
      atTop (𝓝 (2*endpointC b/3)):=by
    have h:=(((tendsto_const_nhds (x:=2*endpointC b/3)).add (hi.const_mul
      (endpointH b+endpointA b/2-2*endpointC b))).add
      ((hi.pow 2).const_mul (-3*endpointH b+endpointA b/2+endpointB b+4*endpointC b/3)))
    simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at h
    apply (tendsto_congr' ?_).mpr h
    filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
    have hkn:(k:ℝ)≠0:=by exact_mod_cast (show k≠0 by omega)
    unfold endpointEPoly
    field_simp
  have hc:2*endpointC b/3=2/(3*(b+3)*(2*b+3)):=by
    unfold endpointC endpointA
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [← hc]
  have h:=hp.add hr
  simp only [add_zero] at h
  apply (tendsto_congr (fun k=>?_)).mpr h
  rw [← endpointEnergy_kernel]
  ring

end
end jacobi.Applications

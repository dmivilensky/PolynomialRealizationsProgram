import jacobi.Analytic.ReferenceNormFactorBounds

/-!
Article: jacobi, Lemma C.1.
The genuine printed continued reference norm has its exact leading
coefficient uniformly on every compact subset of Re(gamma)>0. The
proof controls the actual complex error, including its phase.
Use: Article checks the full uniform asymptotic for the same Gamma norm
already identified with the original complex bilinear integral.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine printed complex reference norms have exactly the claimed leading constant uniformly on every compact admissible order set.
Use: Article checks the complete compact-uniform asymptotic clause of Reference data for the actual Gamma norm, whose equality with the original bilinear integral is already proved.
Article: jacobi, Lemma C.1.
Proof: compactness bounds the original exponent and gives a positive lower bound for the genuine Gamma denominator. The parameter-independent Euler error integral tends to zero. Exact Gamma recurrence factorization leaves only an affine correction and a positive-base complex-power correction, both with explicit uniform inverse-index errors. Their three-factor error tends to zero. -/
theorem norming_asymptotic_uniform {K:Set ℂ} (hK:IsCompact K) (hpos:∀a∈K,0<(gamma a).re) :
    TendstoUniformlyOn (fun n:ℕ=>fun a:ℂ=>scaledNorming a n/normConstant a)
      (fun _=>1) atTop K := by
  -- All compactness bounds apply to the original actual norming factors, rather than to a separately prescribed asymptotic sequence.
  rw [Metric.tendstoUniformlyOn_iff]
  by_cases hne:K.Nonempty
  · have hg:Continuous gamma:=by unfold gamma; fun_prop
    obtain ⟨a0,ha0,hmin⟩:=hK.exists_isMinOn hne (Complex.continuous_re.comp hg).continuousOn
    let d:ℝ:=(gamma a0).re
    have hd:0<d:=hpos a0 ha0
    have hdg (a:ℂ) (ha:a∈K):d≤(gamma a).re:=hmin ha
    obtain ⟨B0,hB0⟩:=hK.exists_bound_of_continuousOn hg.continuousOn
    let B:ℝ:=|B0|+1
    have hB:0<B:=by dsimp [B]; positivity
    have hBg (a:ℂ) (ha:a∈K):‖gamma a‖≤B:=(hB0 a ha).trans (by dsimp [B]; linarith [le_abs_self B0])
    have h2g (a:ℂ) (ha:a∈K):0<(2*gamma a).re:=by norm_num; linarith [hpos a ha]
    obtain ⟨c,C,hc,_,hGamma⟩:=compact_nonzero_norm_bounds hK hne
      (f:=fun a:ℂ=>Complex.Gamma (2*gamma a))
      (fun a ha=>by
        have hh:ContinuousAt (fun z:ℂ=>2*gamma z) a:=by fun_prop
        exact ((gamma_analytic (h2g a ha)).continuousAt.comp_of_eq hh rfl).continuousWithinAt)
      (fun a ha=>Complex.Gamma_ne_zero_of_re_pos (h2g a ha))
    let e (n:ℕ):ℝ:= jacobi.Analysis.gammaEulerError (2*d) (2*B) n/c
    let f (n:ℕ):ℝ:=B/(n:ℝ)
    let h (n:ℕ):ℝ:=4*B/(n:ℝ)
    let E (n:ℕ):ℝ:=e n*(1+f n)*(1+h n)+f n*(1+h n)+h n
    have he:Tendsto e atTop (𝓝 0):=by
      simpa only [zero_div] using (jacobi.Analysis.gammaEuler_error_limit (by positivity : 0<2*d)
        (by positivity : 0<2*B)).div_const c
    have hf:Tendsto f atTop (𝓝 0):=tendsto_natCast_atTop_atTop.const_div_atTop B
    have hh:Tendsto h atTop (𝓝 0):=tendsto_natCast_atTop_atTop.const_div_atTop (4*B)
    have hE:Tendsto E atTop (𝓝 0):=by
      have ht:=((he.mul ((tendsto_const_nhds (x:=(1:ℝ))).add hf)).mul ((tendsto_const_nhds (x:=(1:ℝ))).add hh)).add
        ((hf.mul ((tendsto_const_nhds (x:=(1:ℝ))).add hh)).add hh)
      norm_num at ht
      simpa only [E,add_assoc] using ht
    intro eps heps
    filter_upwards [hE.eventually (Iio_mem_nhds heps),eventually_ge_atTop (1:ℕ),
      eventually_ge_atTop ⌈2*B⌉₊] with n hn hnp hnB a ha
    have hnpos:0<n:=by omega
    have hslo:2*d≤(2*gamma a).re:=by norm_num; linarith [hdg a ha]
    have hsup:(2*gamma a).re≤2*B:=by
      norm_num
      linarith [(Complex.re_le_norm (gamma a)).trans (hBg a ha)]
    have hge:= jacobi.Analysis.gammaEuler_error_bound (by positivity : 0<2*d)
      (by positivity : 0<2*B) hslo hsup (show n≠0 by omega)
    have hgenonneg:0≤ jacobi.Analysis.gammaEulerError (2*d) (2*B) n:=(norm_nonneg _).trans hge
    have hA:‖Complex.GammaSeq (2*gamma a) n/Complex.Gamma (2*gamma a)-1‖≤e n:=by
      have hnz:Complex.Gamma (2*gamma a)≠0:=Complex.Gamma_ne_zero_of_re_pos (h2g a ha)
      rw [show Complex.GammaSeq (2*gamma a) n/Complex.Gamma (2*gamma a)-1=
        (Complex.GammaSeq (2*gamma a) n-Complex.Gamma (2*gamma a))/Complex.Gamma (2*gamma a) by field_simp]
      rw [norm_div]
      exact (div_le_div_of_nonneg_right hge (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left hgenonneg hc (hGamma a ha).1)
    rw [dist_comm,dist_eq_norm,scaledNorming_euler_factorization (hpos a ha) hnpos]
    exact (norm_three_factor_error hA (normAffineFactor_error (hpos a ha) (hBg a ha) hnpos)
      (normPowerFactor_error (hBg a ha) hnpos (Nat.ceil_le.mp hnB))).trans_lt hn
  · intro eps _
    exact Eventually.of_forall (fun _ a ha=>False.elim (hne ⟨a,ha⟩))

end
end jacobi.ComplexReference

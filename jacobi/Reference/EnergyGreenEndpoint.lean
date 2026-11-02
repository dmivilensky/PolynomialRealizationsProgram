import jacobi.Reference.EnergyGreenFactorization
import jacobi.Analysis.PowerPrimitive

/-!
Article: jacobi, Proposition C.4.
The actual Green diagonal has its exact linear leading coefficient
for gamma>1/2 and its exact logarithmic coefficient at gamma=1/2.
The Wronskian ratio derivative and the already proved selected branch
give these limits directly, without a formal differentiation of an
asymptotic expansion or an extra reduction-of-order assumption.
Use: energyGreen_diagonal_limit and its critical counterpart use the same genuine selected solution appearing in the original Green factor.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual real selected reference branch has normalized endpoint limit one at every real energy.
Use: energyGreen_diagonal_limit and its critical counterpart use the same genuine selected solution appearing in the original Green factor.
Article: jacobi, Proposition C.4.
Proof: take the real part of the already proved actual complex-energy endpoint limit; division by a real power commutes with that real part. -/
theorem realSolution_endpoint_limit (a E : ℝ) :
    Tendsto (fun t : ℝ => realSolution a E t/t^(gamma a)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  simpa only [Function.comp_def,realSolution,Complex.div_ofReal_re,Complex.one_re] using
    Complex.continuous_re.continuousAt.tendsto.comp (solution_endpoint_limit a (E:ℂ))

/-- The genuine selected real solution is positive sufficiently close to the physical left endpoint.
Use: energyGreenRatio_hasDerivAt divides only by a nonzero actual selected solution on the original endpoint filter.
Article: jacobi, Proposition C.4.
Proof: the actual ratio to the positive power tends to one and is eventually positive. -/
theorem realSolution_eventually_pos (a E : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),0<realSolution a E t := by
  filter_upwards [(realSolution_endpoint_limit a E).eventually
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<1)),self_mem_nhdsWithin] with t ht htp
  have h := (lt_div_iff₀ (Real.rpow_pos_of_pos htp (gamma a))).mp ht
  simpa only [zero_mul] using h

/-- The genuine real selected solution has its actual real spatial slope as derivative.
Use: energyGreenRatio_hasDerivAt differentiates the source's actual solution quotient.
Article: jacobi, Proposition C.4.
Proof: compose the original complex-valued spatial derivative with the continuous real-part linear map. -/
theorem realSolution_hasDerivAt (a E : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (realSolution a E) (realSlope a E t) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (solution_hasDerivAt a (E:ℂ) ht)

/-- The true reflected-to-selected solution ratio, divided by its fixed genuine Green Wronskian.
Use: the exact diagonal is f(t,E)^2 times this ratio, and its genuine derivative determines both endpoint regimes in Appendix C.5.
Article: jacobi, Proposition C.4.
-/
def energyGreenRatio (a E t : ℝ) : ℝ :=
  realSolution a E (1-t)/(energyGreenConstant a E*realSolution a E t)

/-- The original Green solution ratio has precisely derivative minus the inverse selected-solution square.
Use: energyGreen_diagonal_limit and energyGreen_diagonal_critical_limit integrate the actual source ratio, without an assumed primitive formula.
Article: jacobi, Proposition C.4.
Proof: differentiate the actual quotient, use the proved constant Wronskian identity and cancel only its genuine nonzero denominator and selected solution. -/
theorem energyGreenRatio_hasDerivAt {a E t : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0)
    (ht : t∈Ioo (0:ℝ) 1) (hf : realSolution a E t≠0) :
    HasDerivAt (energyGreenRatio a E) (-1/(realSolution a E t)^2) t := by
  -- The normalization and the two actual derivatives have already been established independently.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hg := (realSolution_hasDerivAt a E hr).comp t ((hasDerivAt_id t).const_sub 1)
  have h := hg.div ((realSolution_hasDerivAt a E ht).const_mul (energyGreenConstant a E))
    (mul_ne_zero (energyGreenConstant_ne_zero ha hE) hf)
  convert h using 1
  · rfl
  · have hW := energyGreenConstant_at (E := E) ha ht
    simp only [mul_neg_one,Function.comp_def]
    field_simp [energyGreenConstant_ne_zero ha hE,hf]
    linear_combination hW

/-- The actual ratio derivative has its exact normalized singular power coefficient minus one.
Use: the same proved derivative limit feeds the linear and logarithmic diagonal regimes of the zero-energy Green lemma.
Article: jacobi, Proposition C.4.
Proof: square the genuine selected endpoint ratio, invert its nonzero limit and identify the actual positive-axis power quotient. -/
theorem energyGreenRatio_derivative_limit (a E : ℝ) :
    Tendsto (fun t : ℝ => t^(2*gamma a)*(-1/(realSolution a E t)^2))
      (𝓝[>] (0:ℝ)) (𝓝 (-1)) := by
  -- The normalization comes solely from the original selected branch coefficient one.
  have h := (((realSolution_endpoint_limit a E).pow 2).inv₀ (by norm_num)).neg
  norm_num only [one_pow,inv_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp := (Real.rpow_pos_of_pos ht (gamma a)).ne'
  have hf : (t^(gamma a))^2=t^(2*gamma a) := by
    rw [show 2*gamma a=gamma a*2 by ring,Real.rpow_mul ht.le,Real.rpow_two]
  rw [div_pow,inv_div,hf]
  ring

/-- The actual Green diagonal has the exact source linear endpoint coefficient for every gamma>1/2 and every reference energy below tau_1.
Use: its E=0 specialization is Appendix C.5's supercritical asymptotic, and Proposition C.4 compares the genuine transformed profile with this same reference diagonal.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual Wronskian ratio derivative has normalized coefficient minus one. The power-primitive theorem gives its coefficient 1/(2*gamma-1); multiply by the square of the genuine selected branch ratio to identify the original Green diagonal. -/
theorem energyGreen_diagonal_limit {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0)
    (hg : 1/2<gamma a) :
    Tendsto (fun t : ℝ => energyGreenKernel a E t t/t) (𝓝[>] (0:ℝ))
      (𝓝 (1/(2*gamma a-1))) := by
  -- All derivative and positivity conditions hold on the actual positive endpoint filter.
  have hd : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),HasDerivAt (energyGreenRatio a E)
      (-1/(realSolution a E t)^2) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),realSolution_eventually_pos a E] with t ht hf
    exact energyGreenRatio_hasDerivAt ha hE ht hf.ne'
  have hl : Tendsto (fun t : ℝ => t^(1-(1-2*gamma a))*(-1/(realSolution a E t)^2))
      (𝓝[>] (0:ℝ)) (𝓝 (-1)) := by
    simpa only [show 1-(1-2*gamma a)=2*gamma a by ring] using energyGreenRatio_derivative_limit a E
  have hratio := jacobi.Analysis.power_endpoint_limit (p := 1-2*gamma a) (by linarith) hd hl
  have hv : (-1:ℝ)/(1-2*gamma a)=1/(2*gamma a-1) := by
    rw [show 1-2*gamma a=-(2*gamma a-1) by ring,neg_div_neg_eq]
  rw [hv] at hratio
  have h := ((realSolution_endpoint_limit a E).pow 2).mul hratio
  simp only [one_pow,one_mul] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),realSolution_eventually_pos a E] with t ht hf
  rw [energyGreen_factorization ha hE ⟨ht.1.le,ht.2.le⟩ ⟨ht.1.le,ht.2.le⟩]
  simp only [energyGreenFactor,min_self,max_self,energyGreenRatio]
  have hp : (t^(gamma a))^2*t^(1-2*gamma a)=t := by
    rw [← Real.rpow_two (t^(gamma a)),← Real.rpow_mul ht.1.le,
      ← Real.rpow_add ht.1,show gamma a*2+(1-2*gamma a)=1 by ring,Real.rpow_one]
  field_simp [(energyGreenConstant_ne_zero ha hE),hf.ne',(Real.rpow_pos_of_pos ht.1 (gamma a)).ne',ht.1.ne',
    (Real.rpow_pos_of_pos ht.1 (1-2*gamma a)).ne']
  linear_combination -(realSolution a E (1-t))*hp

/-- At the critical selected exponent the actual Green diagonal has exactly the source logarithmic leading coefficient one.
Use: completes the critical endpoint asymptotic in Appendix C.5 for the same original selected factor and its full spectral series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the normalized actual ratio derivative has t*R'(t) tending to minus one. The logarithmic primitive theorem determines R/log(t); multiply by the square of the genuine selected branch ratio and use log(1/t)=-log(t). -/
theorem energyGreen_diagonal_critical_limit {a E : ℝ} (ha : -1<a)
    (hE : E<eigenvalue a 0) (hg : gamma a=1/2) :
    Tendsto (fun t : ℝ => energyGreenKernel a E t t/(t*log (1/t)))
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
  -- The same actual Wronskian quotient gives the logarithmic regime without a separate elliptic-function expansion.
  have hd : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),HasDerivAt (energyGreenRatio a E)
      (-1/(realSolution a E t)^2) t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),realSolution_eventually_pos a E] with t ht hf
    exact energyGreenRatio_hasDerivAt ha hE ht hf.ne'
  have hl : Tendsto (fun t : ℝ => t*(-1/(realSolution a E t)^2))
      (𝓝[>] (0:ℝ)) (𝓝 (-1)) := by
    simpa only [hg,show (2:ℝ)*(1/2)=1 by ring,Real.rpow_one] using energyGreenRatio_derivative_limit a E
  have hr := jacobi.Analysis.logarithmic_endpoint_limit hd hl
  have h := (((realSolution_endpoint_limit a E).pow 2).mul hr).neg
  norm_num only [one_pow,one_mul,neg_neg] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),realSolution_eventually_pos a E] with t ht hf
  rw [energyGreen_factorization ha hE ⟨ht.1.le,ht.2.le⟩ ⟨ht.1.le,ht.2.le⟩]
  simp only [energyGreenFactor,min_self,max_self,energyGreenRatio,one_div,Real.log_inv]
  have hp : (t^(gamma a))^2=t := by
    rw [← Real.rpow_two (t^(gamma a)),← Real.rpow_mul ht.1.le,hg,
      show (1/2:ℝ)*2=1 by ring,Real.rpow_one]
  rw [div_pow,hp]
  field_simp [energyGreenConstant_ne_zero ha hE,hf.ne',ht.1.ne']

/-- The zero-energy selected factor has exactly the original printed reference Green series on the whole closed physical square.
Use: this is the literal energy-zero identity used in Proposition C.4, distinct from the earlier factorization at c_0.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: specialize the proved arbitrary-energy complete Green factorization to zero and unfold its original spectral summands. -/
theorem zeroEnergyGreen_formula {a t s : ℝ} (ha : -1<a) (h0 : 0<eigenvalue a 0)
    (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1) :
    realSolution a 0 (min t s)*realSolution a 0 (1-max t s)/energyGreenConstant a 0=
      ∑' k : ℕ,eigenfunction a k t*eigenfunction a k s/(norming a k*eigenvalue a k) := by
  simpa only [energyGreenKernel,energyGreenFactor,energyGreenTerm,sub_zero] using
    (energyGreen_factorization ha h0 ht hs).symm

end
end jacobi.Reference

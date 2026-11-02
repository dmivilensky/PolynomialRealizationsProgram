import jacobi.Reference.GreenIdentity
import jacobi.Reference.RealSpectralDerivatives
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
Article: jacobi, Proposition C.2.
Use: the reference slope and finite transformed endpoint estimates combine powers with different exponents without imposing gamma at least one.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- A larger physical power is bounded by a smaller power near the original positive zero endpoint.
Use: the reference slope and finite transformed endpoint estimates combine powers with different exponents without imposing gamma at least one.
Article: jacobi, Proposition C.2.
Source: monotonicity of real powers on (0,1].
Proof: on the actual positive neighborhood (0,1), exponent monotonicity bounds the genuine power with constant one. -/
theorem endpointPower_bigO {p q : ℝ} (hqp : q≤p) :
    (fun t : ℝ => t^p)=O[𝓝[>] 0](fun t : ℝ => t^q) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  rw [one_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos ht.1 _),
    abs_of_pos (Real.rpow_pos_of_pos ht.1 _)]
  exact Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2.le hqp

/-- Products of genuine endpoint power bounds add their original exponents.
Use: finite coefficient, product primitive and Wronskian estimates use the unchanged selected physical powers.
Article: jacobi, Proposition C.2.
Source: multiplication of Landau bounds and the real power addition identity.
Proof: multiply the community bounds and identify the product of the two actual positive-axis powers with the power of the sum. -/
theorem endpointBigO_mul {R : Type*} [NormedRing R] {f g : ℝ→R} {p q : ℝ}
    (hf : f=O[𝓝[>] 0](fun t : ℝ => t^p)) (hg : g=O[𝓝[>] 0](fun t : ℝ => t^q)) :
    (fun t => f t*g t)=O[𝓝[>] 0](fun t : ℝ => t^(p+q)) := by
  apply (hf.mul hg).congr' EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (Real.rpow_add ht p q).symm

/-- The actual reference solution has its original selected endpoint power bound at arbitrary complex energy.
Use: the true finite feature primitives and transformed Wronskian boundary terms retain the original normalized singular branch.
Article: jacobi, Proposition C.2.
Proof: the original regular factor is analytic and hence locally bounded at zero. Multiply its genuine bound by the unchanged positive-axis power and substitute the independently proved actual selected factorization. -/
theorem solution_endpoint_bigO (a : ℝ) (z : ℂ) :
    solution a z=O[𝓝[>] 0](fun t : ℝ => t^(gamma a)) := by
  have hG := ((solutionFactor_analytic a z).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).isBigO_one ℝ
  have h := (isBigO_refl (fun t : ℝ => t^(gamma a)) (𝓝[>] 0)).smul hG
  simp only [smul_eq_mul,mul_one] at h
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  simpa only [Complex.real_smul] using (solution_factor a z ht).symm

/-- The actual reference spatial slope has its full selected singular power bound at arbitrary complex energy.
Use: the genuine finite transformed Wronskian estimates handle the whole original gamma greater than one quarter range, including an unbounded reference slope at zero.
Article: jacobi, Proposition C.2.
Proof: the original regular factor and its actual derivative are analytic and locally bounded. Differentiate the already proved selected factorization, then compare its second term's higher power with the original gamma-minus-one power on the positive axis. -/
theorem solutionSlope_endpoint_bigO (a : ℝ) (z : ℂ) :
    solutionSlope a z=O[𝓝[>] 0](fun t : ℝ => t^(gamma a-1)) := by
  -- The true original derivative factorization, rather than a formal derivative of an asymptotic expansion, supplies both terms.
  have hG := ((solutionFactor_analytic a z).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).isBigO_one ℝ
  have hG1 := (((solutionFactor_analytic a z).deriv).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).isBigO_one ℝ
  have h0 := ((isBigO_refl (fun t : ℝ => t^(gamma a-1)) (𝓝[>] 0)).smul hG).const_smul_left (gamma a)
  have h1 := ((isBigO_refl (fun t : ℝ => t^(gamma a)) (𝓝[>] 0)).smul hG1)
  simp only [smul_eq_mul,mul_one] at h0 h1
  have h := h0.add (h1.trans (endpointPower_bigO (by linarith : gamma a-1≤gamma a)))
  apply h.congr' ?_ EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),
    (solutionFactor_analytic a z).eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with t ht hg
  rw [solutionSlope_factor a z ht hg.differentiableAt]
  simp only [Pi.smul_apply,Complex.real_smul]
  push_cast
  ring

/-- The true real-energy selected solution has the same original endpoint power bound.
Use: actual finite spectral feature values and their original coefficient sources inherit the complex reference estimate with no new endpoint assumptions.
Article: jacobi, Proposition C.2.
Proof: compose the genuine arbitrary-energy source bound with the bounded real-part map, which is the original real selected solution. -/
theorem realSolution_endpoint_bigO (a E : ℝ) :
    realSolution a E=O[𝓝[>] 0](fun t : ℝ => t^(gamma a)) := by
  unfold realSolution
  exact (Complex.reCLM.isBigO_comp (solution a (E:ℂ)) (𝓝[>] 0)).trans (solution_endpoint_bigO a (E:ℂ))

/-- The genuine real selected slope has the original singular gamma-minus-one power bound.
Use: the actual original finite source slope and inverse-system coefficient slope estimates use this same true reference derivative.
Article: jacobi, Proposition C.2.
Proof: the actual real slope is the bounded real part of the independently proved original complex solution slope. -/
theorem realSlope_endpoint_bigO (a E : ℝ) :
    realSlope a E=O[𝓝[>] 0](fun t : ℝ => t^(gamma a-1)) := by
  unfold realSlope
  exact (Complex.reCLM.isBigO_comp (solutionSlope a (E:ℂ)) (𝓝[>] 0)).trans (solutionSlope_endpoint_bigO a (E:ℂ))

end
end jacobi.Reference

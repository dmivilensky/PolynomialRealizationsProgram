import chebyshev2.Comparison.SymmetricObservation
import chebyshev2.Filters.LinearEnergy

/-!
Article: chebyshev2, Theorem 5.1.
Lemma 14's square-trace formula.
Use: `chebyshev2.Comparison.symmetric_square_trace` feeds
`chebyshev2.Comparison.symmetric_square_trace_support` (symmetric square trace support).
Proof chain: `chebyshev2.Primal.square_trace_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Filters chebyshev2.Continuum chebyshev2.GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x)
  (hc : Continuous m) (hSym : ∀ x, m (-x)=m x)
include hm hn hc hSym

/--
The precise assertion is `(∫ x, (causal 2 m x)^2)= 2*(∫ x in Iic (0:ℝ), (causal 2 m
x)^2)+(causal 2 m 0)^2`.

Use: `chebyshev2.Comparison.symmetric_square_trace` rewrites with this identity to
establish the precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn
j^2)= 2*(∫ x in Iic (0:ℝ), (linear hm hn x)^2)+(linear hm hn 0)^2`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem symmetric_causal_square :
    (∫ x, (causal 2 m x)^2)=
      2*(∫ x in Iic (0:ℝ), (causal 2 m x)^2)+(causal 2 m 0)^2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let U : ℝ → ℝ := fun x => (causal 2 m x+causal 2 m (-x))^2
  let D : ℝ → ℝ := fun x => 4*((causal 2 m (-x))^2-(causal 2 m x)^2)
  have hi := causal_square_integrable hm hn
  -- Establish hir as the integrability justification for the later integral estimates or
  -- changes of order.
  have hir : Integrable (fun x => (causal 2 m (-x))^2) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hi
  -- Establish hD as the integrability justification for the later integral estimates or
  -- changes of order.
  have hD : Integrable D := (hir.sub hi).const_mul 4
  have hd (x : ℝ) : HasDerivAt U (D x) x := by
    have h1 := causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) x
    have h2 := (causal_hasDerivAt hm hc (by norm_num : (0:ℝ) ≤ 2) (-x)).comp x
      (hasDerivAt_id x).neg
    rw [hSym x] at h2
    convert (h1.add h2).pow 2 using 1
    · rfl
    · dsimp [D]
      ring
  -- Record the convergence hU with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hU : Tendsto U atBot (𝓝 0) := by
    have ht := (causal_tendsto_atBot (by norm_num : (0:ℝ) ≤ 2) hm).add
      ((causal_tendsto_atTop (by norm_num : (0:ℝ) < 2) hm).comp tendsto_neg_atBot_atTop)
    simpa only [Function.comp_def,zero_add,zero_pow (by decide : 2 ≠ 0)] using ht.pow 2
  have he : (∫ x in Iic (0:ℝ), D x)=U 0 := by
    have ht := intervalIntegral_tendsto_integral_Iic (0:ℝ) hD.integrableOn tendsto_id
    have hf : (fun a : ℝ => ∫ x in a..0, D x)=fun a => U 0-U a := by
      funext a
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hD.intervalIntegrable
    simp only [id_eq] at ht
    rw [hf] at ht
    exact tendsto_nhds_unique ht (by simpa only [sub_zero] using hU.const_sub (U 0))
  have hs : (∫ x in Iic (0:ℝ), (causal 2 m (-x))^2)=
      ∫ x in Ioi (0:ℝ), (causal 2 m x)^2 := by
    simpa only [neg_zero] using integral_comp_neg_Iic (0:ℝ) (fun x => (causal 2 m x)^2)
  change (∫ x in Iic (0:ℝ), 4*((causal 2 m (-x))^2-(causal 2 m x)^2))=_ at he
  rw [integral_const_mul,integral_sub hir.integrableOn hi.integrableOn,hs] at he
  dsimp [U] at he
  simp only [neg_zero] at he
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn (b := 0)]
  nlinarith

/--
The precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)= 2*(∫
x in Iic (0:ℝ), (linear hm hn x)^2)+(linear hm hn 0)^2`.

Use: `chebyshev2.Comparison.symmetric_square_trace_support` rewrites with this identity to
establish the precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn
j^2)= 2*(∫ x in a..0, (linear hm hn x)^2)+(linear hm hn 0)^2`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.square_trace_cubic`.

Proof: Use the identities/estimates `chebyshev2.Filters.linear_square_trace`,
`chebyshev2.Comparison.symmetric_causal_square` with the arguments shown in the proof.
-/
theorem symmetric_square_trace :
    (groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)=
      2*(∫ x in Iic (0:ℝ), (linear hm hn x)^2)+(linear hm hn 0)^2 := by
  rw [← linear_square_trace hm hn]
  simp only [linear,mul_pow,integral_const_mul]
  rw [symmetric_causal_square hm hn hc hSym]
  ring

end
end chebyshev2.Comparison

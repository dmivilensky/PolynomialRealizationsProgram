import chebyshev2.Comparison.SymmetricSupport
import chebyshev2.Filters.Translation

/-!
Article: chebyshev2, Lemma 14.
Lemma 14 at an arbitrary symmetry center, in the article's original spatial coordinates.
Result: `chebyshev2.Comparison.symmetric_square_trace_support_at` supplies the stated article
conclusion.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Filters chebyshev2.Continuum chebyshev2.GroundState
set_option backward.isDefEq.respectTransparency false
variable {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) (hc : Continuous m)
  (c : ℝ) (hSym : ∀ x, m (2*c-x)=m x)
include hm hn hc hSym

/--
The precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in Iic c, nonlinear
s m x)+log (1+nonlinear s m c)`.

Use: `chebyshev2.Comparison.symmetric_logDeterminant_support_at` rewrites with this
identity to establish `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫
x in a..c, nonlinear s m x)+log (1+nonlinear s m c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_logDeterminant_support_at`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem symmetric_logDeterminant_at {s : ℝ} (hs : 0 ≤ s) :
    logDeterminant (kernelEigenvalue hm hn) s=
      2*(∫ x in Iic c, nonlinear s m x)+log (1+nonlinear s m c) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let n := fun x => m (x+c)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable n := hm.comp_add_right c
  have hp : ∀ x, 0 ≤ n x := fun x => hn _
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous n := hc.comp (continuous_id.add continuous_const)
  have heven : ∀ x, n (-x)=n x := by
    intro x
    change m (-x+c)=m (x+c)
    rw [show -x+c=2*c-(x+c) by ring]
    exact hSym (x+c)
  have h := symmetric_logDeterminant hi hp hcont hs heven
  have hf : nonlinear s n=fun x => nonlinear s m (x+c) := funext (nonlinear_translate hm hn hs c)
  have hobs : logDeterminant (kernelEigenvalue hi hp) s=logDeterminant (kernelEigenvalue hm hn) s := by
    rw [← nonlinear_mass_eq_logDeterminant hi hp hs,hf,integral_add_right_eq_self,
      nonlinear_mass_eq_logDeterminant hm hn hs]
  rw [hobs,hf,integral_Iic_translate,zero_add] at h
  simpa only [zero_add] using h

/--
The precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)= 2*(∫
x in Iic c, (linear hm hn x)^2)+(linear hm hn c)^2`.

Use: `chebyshev2.Comparison.symmetric_square_trace_support_at` rewrites with this identity
to establish `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm
hn j^2)= 2*(∫ x in a..c, (linear hm hn x)^2)+(linear hm hn c)^2`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_square_trace_support_at`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem symmetric_square_trace_at :
    (groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)=
      2*(∫ x in Iic c, (linear hm hn x)^2)+(linear hm hn c)^2 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let n := fun x => m (x+c)
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable n := hm.comp_add_right c
  have hp : ∀ x, 0 ≤ n x := fun x => hn _
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous n := hc.comp (continuous_id.add continuous_const)
  have heven : ∀ x, n (-x)=n x := by
    intro x
    change m (-x+c)=m (x+c)
    rw [show -x+c=2*c-(x+c) by ring]
    exact hSym (x+c)
  have h := symmetric_causal_square hi hp hcont heven
  have hf : causal 2 n=fun x => causal 2 m (x+c) := funext (causal_translate m 2 c)
  rw [hf] at h
  change (∫ x, (causal 2 m (x+c))^2)=2*(∫ x in Iic (0:ℝ), (causal 2 m (x+c))^2)+
    (causal 2 m (0+c))^2 at h
  rw [integral_add_right_eq_self (fun x => (causal 2 m x)^2) c,
    integral_Iic_translate (fun x => (causal 2 m x)^2) c 0,zero_add] at h
  rw [← linear_square_trace hm hn]
  simp only [linear,mul_pow,integral_const_mul]
  rw [h]
  ring

omit hm hn hc hSym in
/--
Exact identity `(∫ x in Iic c, f x)=∫ x in a..c, f x`.

Use: `chebyshev2.Comparison.symmetric_logDeterminant_support_at` rewrites with this
identity to establish `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫
x in a..c, nonlinear s m x)+log (1+nonlinear s m c)`.

Article: chebyshev2, Lemma 14 via
`chebyshev2.Comparison.symmetric_logDeterminant_support_at`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem halfLine_eq_support_interval_at {f : ℝ → ℝ} (hf : Integrable f) (a c : ℝ)
    (hz : ∀ x ≤ a, f x=0) : (∫ x in Iic c, f x)=∫ x in a..c, f x := by
  have he : (∫ x in Iic a, f x)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    exact hz x hx
  have h := intervalIntegral.integral_Iic_sub_Iic (a := a) (b := c) hf.integrableOn hf.integrableOn
  simpa only [he,sub_zero] using h

/--
The precise assertion is `logDeterminant (kernelEigenvalue hm hn) s= 2*(∫ x in a..c, nonlinear
s m x)+log (1+nonlinear s m c)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 14.

Proof: Use the identities/estimates `chebyshev2.Comparison.symmetric_logDeterminant_at`,
`chebyshev2.Comparison.halfLine_eq_support_interval_at`,
`chebyshev2.Filters.nonlinear_integrable` with the arguments shown in the proof.
-/
theorem symmetric_logDeterminant_support_at {s : ℝ} (hs : 0 ≤ s) (a : ℝ)
    (hz : ∀ x ≤ a, m x=0) :
    logDeterminant (kernelEigenvalue hm hn) s=
      2*(∫ x in a..c, nonlinear s m x)+log (1+nonlinear s m c) := by
  rw [symmetric_logDeterminant_at hm hn hc c hSym hs,
    halfLine_eq_support_interval_at (nonlinear_integrable hm hn hs) a c
      (fun x hx => nonlinear_left_of_density_zero x s (fun t ht => hz t (ht.trans hx)))]

/--
The precise assertion is `(groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)= 2*(∫
x in a..c, (linear hm hn x)^2)+(linear hm hn c)^2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 14.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem symmetric_square_trace_support_at (a : ℝ) (hz : ∀ x ≤ a, m x=0) :
    (groundParameter hm hn)^2/4*(∑' j, kernelEigenvalue hm hn j^2)=
      2*(∫ x in a..c, (linear hm hn x)^2)+(linear hm hn c)^2 := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi : Integrable (fun x => (linear hm hn x)^2) := by
    simpa only [linear,mul_pow] using (causal_square_integrable hm hn).const_mul
      ((groundParameter hm hn)^2)
  have hz' (x : ℝ) (hx : x ≤ a) : (linear hm hn x)^2=0 := by
    have hj : (∫ t in Iic x, exp (2*t)*m t)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      change exp (2*t)*m t=0
      rw [hz t (ht.trans hx),mul_zero]
    simp [linear,causal,hj]
  rw [symmetric_square_trace_at hm hn hc c hSym,halfLine_eq_support_interval_at hi a c hz']

end
end chebyshev2.Comparison

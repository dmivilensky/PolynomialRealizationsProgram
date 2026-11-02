import jacobi.Hankel.Operator
import jacobi.Hankel.TailPrimitive

/-!
Article: jacobi, Lemma E.1.
Use: outgoingIntegral_fourierTail splits only genuinely convergent original integrals into differentiable Fourier tails.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Euler's exact exponential expression for the original outgoing kernel above its Volterra diagonal.
Use: outgoingIntegral_fourierTail splits only genuinely convergent original integrals into differentiable Fourier tails.
Article: jacobi, Lemma E.1.
Proof: expand the complex sine by its defining exponentials and use exp(w)*exp(-w)=1; the nonzero factor 2i is an ordinary field denominator. -/
theorem outgoingKernel_exponential {d : ℝ} (hd : 0≤d) :
    outgoingKernel d=(Complex.exp (2*(d:ℂ)*Complex.I)-1)/(2*Complex.I) := by
  -- The formula is exact, including the original zero value on the diagonal.
  rw [outgoingKernel_nonneg hd,Complex.ofReal_sin,Complex.sin]
  have hi : (2*Complex.I:ℂ)≠0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (eq_div_iff hi).mpr
  rw [show 2*(d:ℂ)*Complex.I=(d:ℂ)*Complex.I+(d:ℂ)*Complex.I by ring,Complex.exp_add]
  have he : Complex.exp (-(d:ℂ)*Complex.I)*Complex.exp ((d:ℂ)*Complex.I)=1 := by
    rw [← Complex.exp_add]
    simp
  calc
    _ = Complex.exp ((d:ℂ)*Complex.I)*Complex.exp ((d:ℂ)*Complex.I)-
        Complex.exp (-(d:ℂ)*Complex.I)*Complex.exp ((d:ℂ)*Complex.I) := by
      simp only [div_eq_mul_inv]
      linear_combination (Complex.exp (-(d:ℂ)*Complex.I)-Complex.exp ((d:ℂ)*Complex.I))*
        Complex.exp ((d:ℂ)*Complex.I)*Complex.I_sq
    _ = _ := by rw [he]

/-- The genuine complex potential-amplitude product is integrable.
Use: outgoingIntegral_fourierTail and its spatial derivative split the actual improper integral with all convergence hypotheses proved.
Article: jacobi, Lemma E.1.
Proof: multiply the original L1 potential by the bounded continuous amplitude using the community bounded-product integrability theorem. -/
theorem outgoingSource_integrable {m : ℝ → ℝ} (hm : Integrable m) (f : OutgoingSpace) :
    Integrable (fun y : ℝ => (m y:ℂ)*f y) :=
  hm.ofReal.mul_bdd f.continuous.aestronglyMeasurable
    (Eventually.of_forall f.norm_coe_le_norm)

/-- Multiplication by the original oscillatory Fourier factor preserves genuine integrability.
Use: the oscillatory tail in outgoingIntegral_fourierTail has an actual convergent improper integral and the proved FTC derivative.
Article: jacobi, Lemma E.1.
Proof: its multiplier is continuous and has norm exactly one on the original real ray. -/
theorem outgoingFourier_integrable {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun y : ℝ => Complex.exp (2*(y:ℂ)*Complex.I)*g y) := by
  apply hg.bdd_mul (by fun_prop)
  exact Eventually.of_forall (fun y => by
    rw [show 2*(y:ℂ)*Complex.I=((2*y:ℝ):ℂ)*Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I])

/-- The actual outgoing integral is exactly the difference of its oscillatory and nonoscillatory improper Fourier tails.
Use: differentiating the actual two tail primitives proves the outgoing spatial ODE for the very same Banach-inverse amplitude used in the complex-order asymptotics.
Article: jacobi, Lemma E.1.
Proof: the causal kernel vanishes below the moving diagonal. Above it, Euler's identity separates the two original absolutely convergent terms, and their constant spatial Fourier factor is taken outside the integral. -/
theorem outgoingIntegral_fourierTail {m : ℝ → ℝ} (hm : Integrable m)
    (f : OutgoingSpace) (x : ℝ) :
    outgoingIntegral m f x=
      (Complex.exp (-2*(x:ℂ)*Complex.I)*
        tailPrimitive (fun y : ℝ => Complex.exp (2*(y:ℂ)*Complex.I)*((m y:ℂ)*f y)) x-
        tailPrimitive (fun y : ℝ => (m y:ℂ)*f y) x)/(2*Complex.I) := by
  -- Restriction to the original future ray is an exact support identity, not an asymptotic truncation.
  have hsup : (fun y : ℝ => outgoingKernel (y-x)*((m y:ℂ)*f y))=
      (Ioi x).indicator (fun y : ℝ => outgoingKernel (y-x)*((m y:ℂ)*f y)) := by
    funext y
    by_cases hy : x<y
    · simp only [indicator_of_mem (show y∈Ioi x from hy)]
    · rw [indicator_of_notMem (show y∉Ioi x from hy),
        outgoingKernel_zero (sub_nonpos.mpr (not_lt.mp hy)),zero_mul]
  rw [outgoingIntegral,hsup,integral_indicator measurableSet_Ioi]
  have he (y : ℝ) (hy : y∈Ioi x) :
      outgoingKernel (y-x)*((m y:ℂ)*f y)=
      (Complex.exp (-2*(x:ℂ)*Complex.I)*(Complex.exp (2*(y:ℂ)*Complex.I)*((m y:ℂ)*f y))-
        (m y:ℂ)*f y)/(2*Complex.I) := by
    rw [outgoingKernel_exponential (sub_nonneg.mpr hy.le)]
    push_cast
    rw [show 2*((y:ℂ)-x)*Complex.I=(-2*(x:ℂ)*Complex.I)+(2*(y:ℂ)*Complex.I) by ring,
      Complex.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he]
  rw [integral_div,integral_sub
    (((outgoingFourier_integrable (outgoingSource_integrable hm f)).const_mul _).integrableOn)
    ((outgoingSource_integrable hm f).integrableOn),integral_const_mul]
  rfl

end
end jacobi.Hankel

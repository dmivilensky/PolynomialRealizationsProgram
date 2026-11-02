import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
Article: jacobi, Lemma E.1.
Source: variation of constants for y''+(1+c/x^2)*y=0, proved below.
Use: outgoingOperator is a bounded operator on bounded continuous complex functions, with norm controlled only by the L1 norm of the inverse-square potential.
-/
namespace jacobi.Hankel
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology

/-- The outgoing real-ray Jost integral kernel, with zero on the forbidden side of its Volterra diagonal.
Use: outgoingOperator is a bounded operator on bounded continuous complex functions, with norm controlled only by the L1 norm of the inverse-square potential.
Article: jacobi, Lemma E.1.
-/
def outgoingKernel (d : ℝ) : ℂ :=
  (Real.sin (max 0 d):ℂ)*Complex.exp ((max 0 d:ℝ)*Complex.I)

/-- The genuine outgoing kernel is continuous through the Volterra diagonal.
Use: outgoingIntegral_continuous preserves continuous functions; its parameter continuity and norm estimates do not require an artificial diagonal exclusion.
Article: jacobi, Lemma E.1.
Proof: both factors are continuous functions of the same continuous clipped real argument. -/
theorem outgoingKernel_continuous : Continuous outgoingKernel := by
  unfold outgoingKernel
  fun_prop

/-- The actual outgoing Volterra kernel has the uniform modulus bound one on the whole real line.
Use: outgoingOperator_norm_le and the true Jost Neumann inverse use a bound independent of the order and of both spatial coordinates.
Article: jacobi, Lemma E.1.
Proof: the exponential has purely imaginary argument and therefore unit modulus; the remaining real sine has absolute value at most one. -/
theorem outgoingKernel_norm_le (d : ℝ) : ‖outgoingKernel d‖≤1 := by
  rw [outgoingKernel,norm_mul,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- The outgoing Volterra kernel vanishes on and below its actual diagonal.
Use: the integral operator restricts its potential to y>x automatically, allowing tail bounds at each genuine large spatial point.
Article: jacobi, Lemma E.1.
Proof: clipping a nonpositive argument gives zero and sin(0)=0. -/
theorem outgoingKernel_zero {d : ℝ} (hd : d≤0) : outgoingKernel d=0 := by
  simp only [outgoingKernel,max_eq_left hd,Real.sin_zero,Complex.ofReal_zero,zero_mul]

/-- On the future half-line the genuine kernel is exactly the outgoing oscillatory Green expression.
Use: actual Jost differentiation identifies the constructed inverse with the original inverse-square differential equation.
Article: jacobi, Lemma E.1.
Proof: clipping fixes every nonnegative argument. -/
theorem outgoingKernel_nonneg {d : ℝ} (hd : 0≤d) :
    outgoingKernel d=(Real.sin d:ℂ)*Complex.exp ((d:ℂ)*Complex.I) := by
  rw [outgoingKernel,max_eq_right hd]

/-- The genuine uncut outgoing kernel has derivative exp(2*i*d) on the real ray.
Use: differentiating the actual Volterra equation gives the selected outgoing Jost solution and its derivative remainder, without differentiating a formal asymptotic series.
Article: jacobi, Lemma E.1.
Proof: apply the ordinary product and exponential chain rules, then use Euler's identity to combine cosine plus i*sine into the second exponential. -/
theorem outgoingKernel_hasDerivAt {d : ℝ} (hd : 0<d) :
    HasDerivAt outgoingKernel (Complex.exp (2*(d:ℂ)*Complex.I)) d := by
  -- The clipped and original kernels agree on an actual neighborhood strictly above the diagonal.
  have hs := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt d (Real.hasDerivAt_sin d)
  have he := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt d (hasDerivAt_id d)).mul_const Complex.I).cexp
  have h := hs.mul he
  have hv : ((Real.cos d:ℂ)*Complex.exp ((d:ℂ)*Complex.I)+
      (Real.sin d:ℂ)*(Complex.exp ((d:ℂ)*Complex.I)*Complex.I))=
        Complex.exp (2*(d:ℂ)*Complex.I) := by
    rw [show 2*(d:ℂ)*Complex.I=(d:ℂ)*Complex.I+(d:ℂ)*Complex.I by ring,Complex.exp_add,
      Complex.exp_mul_I]
    simp only [← Complex.ofReal_cos,← Complex.ofReal_sin]
    ring
  have hsame : outgoingKernel=ᶠ[𝓝 d] (fun x : ℝ => (Real.sin x:ℂ)*Complex.exp ((x:ℂ)*Complex.I)) := by
    filter_upwards [Ioi_mem_nhds hd] with x hx
    exact outgoingKernel_nonneg hx.le
  convert h.congr_of_eventuallyEq hsame using 1
  simpa only [Function.comp_def,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,one_mul] using hv.symm

end
end jacobi.Hankel

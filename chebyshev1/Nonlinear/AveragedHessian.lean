import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: chebyshev1, Corollary 5.4.
The factor one half comes from integrating distance along the query segment.
Use: `chebyshev1.Nonlinear.averagedDerivative_sub_norm_le` feeds
`chebyshev1.Nonlinear.lipschitzHessian_error_le` (Corollary 5.4 in coordinates centered at the
stationary point).
-/
namespace chebyshev1.Nonlinear
noncomputable section
open Set MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/--
Defines `averagedDerivative` of type `E →L[ℝ] F` by `∫ t in (0:ℝ)..1, A (x + t • e)`.

Use: `chebyshev1.Nonlinear.averagedDerivative_apply` rewrites with this definition to
establish exact identity `averagedDerivative A x e e = g (x+e) - g x`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.averagedDerivative_apply`.
-/
def averagedDerivative (A : E → E →L[ℝ] F) (x e : E) : E →L[ℝ] F :=
  ∫ t in (0:ℝ)..1, A (x + t • e)

/--
FTC along a segment: the nonlinear gradient equals the averaged Hessian times the error.

Exact identity `averagedDerivative A x e e = g (x+e) - g x`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` uses this identity to establish the
stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem averagedDerivative_apply (g : E → F) (A : E → E →L[ℝ] F) (x e : E)
    (hA : ContinuousOn (fun t : ℝ => A (x+t • e)) (Icc 0 1))
    (hg : ∀ t ∈ Icc (0:ℝ) 1, HasFDerivAt g (A (x+t • e)) (x+t • e)) :
    averagedDerivative A x e e = g (x+e) - g x := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hint := hA.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  rw [averagedDerivative, ContinuousLinearMap.intervalIntegral_apply hint]
  have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun t : ℝ => g (x+t • e)) (A (x+t • e) e) t := by
    have hpath : HasDerivAt (fun t : ℝ => x+t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x
    exact (hg t (by simpa using ht)).comp_hasDerivAt t hpath
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hA.clm_apply continuousOn_const).intervalIntegrable_of_Icc
      (μ := volume) (by norm_num : (0:ℝ) ≤ 1))

/--
The factor one half comes from integrating distance along the query segment.

The stated quantitative bound `‖averagedDerivative A x e - A x‖ ≤ rho * ‖e‖ / 2`.

Use: `chebyshev1.Nonlinear.lipschitzHessian_error_le` uses this bound to establish the
stated quantitative bound `‖errorTrajectory family I N g e0 N‖ ≤ I.epsilon N * (T ℝ N).eval
(1+rho*R/I.delta) * ‖e0‖`.

Article: chebyshev1, Corollary 5.4.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem averagedDerivative_sub_norm_le (A : E → E →L[ℝ] F) (x e : E) (rho : ℝ)
    (hA : ContinuousOn (fun t : ℝ => A (x+t • e)) (Icc 0 1))
    (hlip : ∀ t ∈ Icc (0:ℝ) 1, ‖A (x+t • e) - A x‖ ≤ rho * ‖t • e‖) :
    ‖averagedDerivative A x e - A x‖ ≤ rho * ‖e‖ / 2 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hint := hA.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hc : IntervalIntegrable (fun _ : ℝ => A x) volume 0 1 := intervalIntegrable_const
  have heq : averagedDerivative A x e - A x =
      ∫ t in (0:ℝ)..1, (A (x+t • e)-A x) := by
    rw [intervalIntegral.integral_sub hint hc, intervalIntegral.integral_const]
    simp [averagedDerivative]
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0:ℝ) ≤ 1)
    (f := fun t : ℝ => A (x+t • e)-A x)
    (g := fun t : ℝ => t*(rho*‖e‖))
    (μ := volume)
    (by
      apply Filter.Eventually.of_forall
      intro t ht
      have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2⟩
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1, mul_left_comm,
        mul_comm, mul_assoc] using hlip t ht')
    ((continuous_id.mul continuous_const).intervalIntegrable 0 1)
  convert hb using 1
  rw [intervalIntegral.integral_mul_const, integral_id]
  ring

end
end chebyshev1.Nonlinear

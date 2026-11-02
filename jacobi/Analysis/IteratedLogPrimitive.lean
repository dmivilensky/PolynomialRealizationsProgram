import jacobi.Analysis.AsymptoticSlope
import Mathlib.Topology.Algebra.Order.Field

/-!
Article: jacobi, Proposition C.4.
A derivative of size 1/(t*log(1/t)) has a genuine log-log primitive.
The proof uses the mean-value asymptotic-slope theorem in exponential
coordinates twice; no derivative of an assumed asymptotic is used.
Use: iterated_logarithmic_endpoint_limit integrates the critical packing-coordinate derivative in the coordinate x=log(1/t).
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter
open scoped Topology

/-- A genuine derivative with x*f'(x) tending to L has its exact logarithmic primitive at positive infinity.
Use: iterated_logarithmic_endpoint_limit integrates the critical packing-coordinate derivative in the coordinate x=log(1/t).
Article: jacobi, Proposition C.4.
Source: the mean value theorem in exponential coordinates.
Proof: f(exp(y)) has derivative exp(y)*f'(exp(y)), tending to L. Apply the proved asymptotic-slope theorem, then substitute y=log(x). -/
theorem logarithmic_infinity_limit {f f' : ℝ → ℝ} {L : ℝ}
    (hd : ∀ᶠ x : ℝ in atTop,HasDerivAt f (f' x) x)
    (hl : Tendsto (fun x : ℝ => x*f' x) atTop (𝓝 L)) :
    Tendsto (fun x : ℝ => f x/log x) atTop (𝓝 L) := by
  -- The ordinary derivative, rather than a formal asymptotic expansion, supplies the primitive coefficient.
  have hder : ∀ᶠ y : ℝ in atTop,HasDerivAt (fun y : ℝ => f (exp y))
      (exp y*f' (exp y)) y := by
    filter_upwards [tendsto_exp_atTop.eventually hd] with y hy
    simpa only [Function.comp_def,mul_comm] using hy.comp y (Real.hasDerivAt_exp y)
  have h := (asymptotic_slope hder (hl.comp tendsto_exp_atTop)).comp tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  simp only [Function.comp_def,exp_log hx]

/-- The genuine critical singular derivative determines the exact iterated-logarithmic endpoint primitive.
Use: the actual critical intrinsic coordinate has coefficient -1/2 and therefore an infinite left endpoint and the source doubly exponential density tail.
Article: jacobi, Proposition C.4.
Source: the mean value theorem in the logarithmic coordinate, via logarithmic_infinity_limit.
Proof: compose with t=exp(-x). The resulting derivative multiplied by x tends to -L. Apply the logarithmic primitive at infinity and substitute x=log(1/t) on the genuine positive endpoint filter. -/
theorem iterated_logarithmic_endpoint_limit {f f' : ℝ → ℝ} {L : ℝ}
    (hd : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),HasDerivAt f (f' t) t)
    (hl : Tendsto (fun t : ℝ => (t*log (1/t))*f' t) (𝓝[>] (0:ℝ)) (𝓝 L)) :
    Tendsto (fun t : ℝ => f t/log (log (1/t))) (𝓝[>] (0:ℝ)) (𝓝 (-L)) := by
  -- Exponential substitution converts the true double singularity into the already proved logarithmic primitive at infinity.
  have ht : Tendsto (fun x : ℝ => exp (-x)) atTop (𝓝[>] (0:ℝ)) :=
    tendsto_exp_atBot_nhdsGT.comp tendsto_neg_atTop_atBot
  have hder : ∀ᶠ x : ℝ in atTop,HasDerivAt (fun y : ℝ => f (exp (-y)))
      (-exp (-x)*f' (exp (-x))) x := by
    filter_upwards [ht.eventually hd] with x hx
    convert hx.comp x ((hasDerivAt_id x).neg.exp) using 1
    · rfl
    · dsimp only [Pi.neg_apply,id_eq]
      ring
  have hlim : Tendsto (fun x : ℝ => x*(-exp (-x)*f' (exp (-x)))) atTop (𝓝 (-L)) := by
    convert (hl.comp ht).neg using 1
    ext x
    simp only [Function.comp_def,one_div,Real.log_inv,Real.log_exp,neg_neg]
    ring
  have h := (logarithmic_infinity_limit hder hlim).comp
    (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t htpos
  simp only [Function.comp_def,neg_neg,exp_log htpos,one_div,Real.log_inv]

end
end jacobi.Analysis

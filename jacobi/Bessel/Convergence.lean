import jacobi.Bessel.Coefficients

/-!
Article: jacobi, Proposition A.1.
The original literal coefficients form a genuinely convergent power series
at every complex spectral argument. A formal multilinear power series with
infinite radius is supplied, so all later termwise analytic arguments can
use the actual sum and its actual coefficients together.
Source: mathlib's proved infinite-radius regularized hypergeometric series.
Use: dominated convergence and canonical-product coefficient comparisons may use actual summability.
-/
namespace jacobi.Bessel
noncomputable section
open Complex Set Filter FormalMultilinearSeries
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The normalized Bessel coefficient series genuinely sums to the defined function at every complex point.
Use: dominated convergence and canonical-product coefficient comparisons may use actual summability.
Article: jacobi, Proposition A.1.
Proof: infinite radius gives the actual hypergeometric HasSum at -z/4.
Multiply its convergent sum by the Gamma normalization and collect the
literal coefficient powers, retaining the original function as the sum. -/
theorem normalized_hasSum (a z : ℂ) :
    HasSum (fun n => coefficient a n*z^n) (normalized a z) := by
  -- This proves convergence itself, rather than merely an equality between totalized infinite sums.
  let p := regularizedHGFunSeries (0:Multiset ℂ) {a+1}
  have hp : 0<p.radius := by rw [show p.radius=⊤ from radius a]; exact ENNReal.zero_lt_top
  have hz : -z/4∈Metric.eball (0:ℂ) p.radius := by rw [show p.radius=⊤ from radius a]; simp
  have h := ((p.hasFPowerSeriesOnBall hp).hasSum hz).mul_left (Gamma (a+1))
  simp only [zero_add] at h
  convert h using 1
  · funext n
    rw [show p n (fun _ => -z/4)=regularizedHGFunCoeff 0 {a+1} n*(-z/4)^n by
      exact ofScalars_apply_eq (regularizedHGFunCoeff 0 {a+1}) (-z/4) n]
    unfold coefficient
    rw [show -z/4=(-1/4:ℂ)*z by ring,mul_pow]
    ring
  · rfl

/-- The literal normalized Bessel coefficient power series is absolutely summable at every complex point.
Use: provides genuine summable majorants for the Jacobi-to-Bessel limiting series.
Article: jacobi, Proposition A.1.
Proof: complex summability of the actual series is equivalent to summability of its norms. -/
theorem normalized_norm_summable (a z : ℂ) : Summable (fun n => ‖coefficient a n*z^n‖) :=
  (normalized_hasSum a z).summable.norm

end
end jacobi.Bessel

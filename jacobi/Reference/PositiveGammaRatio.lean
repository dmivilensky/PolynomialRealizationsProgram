import jacobi.Reference.GammaRatio

/-!
Power normalization of Gamma quotients with two positive shifts.
Euler's already proved Gamma limit suffices; a separate Stirling
expansion is unnecessary for the standard Jacobi kernel limit.
Use: StandardAsymptotic evaluates the true endpoint norm and conductance
power laws for arbitrary independent Jacobi parameters.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the Gamma quotient limit behind the standard endpoint power law.
Source: NIST DLMF Section 5.11: the Gamma-ratio asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every genuine Gamma quotient with positive shifts has its exact
unit leading power constant. The finite zero index is irrelevant to the
limit; every cancellation in the positive tail is justified explicitly.
Article: jacobi, Theorem 5.4, Equation (5.10).
Source: NIST DLMF Section 5.11: the Gamma-ratio asymptotic.
-/
theorem positive_gamma_ratio_limit {p q : ℝ} (hp : 0<p) (hq : 0<q) :
    Tendsto (fun n : ℕ => (n:ℝ)^(q-p)*Gamma ((n:ℝ)+p)/Gamma ((n:ℝ)+q))
      atTop (𝓝 1) := by
  have h := ((gamma_ratio_limit hq).div (gamma_ratio_limit hp) one_ne_zero).mul
    (shifted_nat_ratio q p)
  simp only [div_one,mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hnP : 0<(n:ℝ)+p := by positivity
  have hnQ : 0<(n:ℝ)+q := by positivity
  simp only [Pi.div_apply]
  rw [Real.rpow_sub hnR]
  field_simp [(Real.rpow_pos_of_pos hnR p).ne',
    (Real.Gamma_pos_of_pos hnP).ne',(Real.Gamma_pos_of_pos hnQ).ne',
    (Real.Gamma_pos_of_pos (show 0<(n:ℝ)+1 by positivity)).ne',hnP.ne',hnQ.ne']

end
end jacobi.Reference

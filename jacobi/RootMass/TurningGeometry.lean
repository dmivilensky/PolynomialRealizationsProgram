import jacobi.RootMass.TurningRegularity

/-!
Article: jacobi, Appendix D.5.
The turning radicand is positive before the true inverse endpoint and has
an actual simple zero there with strictly negative derivative. Together
with the proved inverse-square-root integrability this closes the endpoint
justification used in every printed profile quadrature.
Source: the literal factorization, actual psi derivative and its proved inverse.
Use: its sign and exact endpoint derivative follow from actual psi monotonicity.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal turning radicand has the printed inverse-coordinate factorization wherever p is nonzero.
Use: its sign and exact endpoint derivative follow from actual psi monotonicity.
Article: jacobi, Appendix D.5.
Proof: clear the nonzero p denominator in the actual rational expression. -/
theorem radicand_factor {a y n : ℝ} (hp : p a n≠0) :
    radicand a y n=(p a n)^2*(1-psi a n/y) := by
  unfold radicand psi
  field_simp

/-- The actual turning radicand is strictly positive up to its genuine upper turning endpoint.
Use: selects the real positive square root in the full turning integral.
Article: jacobi, Appendix D.5.
Proof: strict monotonicity gives psi(n)<psi(n_0)=y, and the positive p² factor preserves its sign. -/
theorem radicand_pos {a y n : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y)
    (hn : n∈Ico (1:ℝ) (inverse a ha y)) : 0<radicand a y n := by
  have hp := (p_bounds ha hn.1).1.trans_le (p_bounds ha hn.1).2.1
  have hpsi := psi_strictMono ha hn.1 (inverse_ge_one a ha y) hn.2
  rw [psi_inverse ha hy.le] at hpsi
  rw [radicand_factor hp.ne']
  exact mul_pos (sq_pos_of_pos hp) (sub_pos.mpr ((div_lt_one hy).mpr hpsi))

/-- The actual inverse endpoint is a genuine zero of the printed turning radicand.
Use: fixes the turning interval independently of the optimizing spatial profile.
Article: jacobi, Appendix D.5.
Proof: the actual inverse gives psi(n_0)=y in the exact positive-denominator factorization. -/
theorem radicand_turning_zero {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    radicand a y (inverse a ha y)=0 := by
  have hn := inverse_ge_one a ha y
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  rw [radicand_factor hp.ne',psi_inverse ha hy.le,div_self hy.ne',sub_self,mul_zero]

/-- The turning zero has its exact classical derivative, with every local identity justified near the actual inverse endpoint.
Use: verifies the source's simple turning zero, in addition to the independently proved integral convergence.
Article: jacobi, Appendix D.5.
Proof: p is nonzero near the actual endpoint, so the exact radicand
factorization holds on a genuine neighborhood. Differentiate its product;
psi(n_0)=y kills the first term and leaves the printed negative derivative. -/
theorem radicand_turning_hasDerivAt {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    HasDerivAt (radicand a y)
      (-(p a (inverse a ha y))^2*psiSlope a (inverse a ha y)/y) (inverse a ha y) := by
  -- The derivative is transferred from an actual local factorization, not a formal identity at a point.
  let n := inverse a ha y
  have hn : 1≤n := inverse_ge_one a ha y
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  have hP : HasDerivAt (p a) (6*n+a) n := by
    convert (((hasDerivAt_id n).pow 2).const_mul 3).add ((hasDerivAt_id n).const_mul a) |>.add_const 1 using 1
    · rfl
    · norm_num; ring
  have hh : HasDerivAt (fun t => (p a t)^2*(1-psi a t/y)) (-(p a n)^2*psiSlope a n/y) n := by
    convert (hP.pow 2).mul (((psi_hasDerivAt hp.ne').div_const y).const_sub 1) using 1
    dsimp only [Pi.pow_apply]
    rw [show psi a n=y from psi_inverse ha hy.le,div_self hy.ne']
    ring
  have he : radicand a y=ᶠ[𝓝 n] fun t => (p a t)^2*(1-psi a t/y) := by
    filter_upwards [hP.continuousAt.eventually (eventually_ne_nhds hp.ne')] with t ht
    exact radicand_factor ht
  exact hh.congr_of_eventuallyEq he

/-- The actual turning zero is simple with strictly negative derivative throughout the stated parameter range.
Use: confirms the exact upper turning geometry in the source profile calculus.
Article: jacobi, Appendix D.5.
Proof: p, psi' and y are genuinely positive at the constructed inverse turning level. -/
theorem radicand_turning_deriv_neg {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    deriv (radicand a y) (inverse a ha y)<0 := by
  rw [(radicand_turning_hasDerivAt ha hy).deriv]
  have hn := inverse_ge_one a ha y
  have hp := (p_bounds ha hn).1.trans_le (p_bounds ha hn).2.1
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hp)) (psiSlope_pos ha hn)) hy

end
end jacobi.RootMass

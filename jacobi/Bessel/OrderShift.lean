import jacobi.Bessel.Differential

/-!
Article: jacobi, Proposition C.4.
The actual normalized spectral Bessel derivative is expressed in the
next order. This proves the source adjacent-order identity from the
same convergent power series already used for the zero enumeration.
Source: the Bessel differentiation identity, DLMF 10.6.2; proved here.
Use: proves normalized_derivative_order_shift for the actual entire functions.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter _root_.Complex FormalMultilinearSeries
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true adjacent-order Bessel coefficients satisfy the exact derivative identity at every degree.
Use: proves normalized_derivative_order_shift for the actual entire functions.
Article: jacobi, Proposition C.4.
Proof: Euler's Gamma recurrence shifts the order normalization, and
the next factorial cancels its genuine n+1 factor. Both series then
have the same literal Gamma denominator and power of -1/4. -/
theorem coefficient_order_shift {a : ℂ} (ha : -1<a.re) (n : ℕ) :
    (n+1:ℂ)*coefficient a (n+1)=(-1/(4*(a+1)))*coefficient (a+1) n := by
  -- Only finite exact Gamma identities are needed before differentiating the genuine series.
  have ha1 : a+1≠0 := by simpa only [Nat.cast_zero,add_zero] using (order_nonzero ha 0).1
  rw [coefficient_formula,coefficient_formula]
  have hden : a+1+((n+1:ℕ):ℂ)=(a+1)+1+(n:ℂ) := by push_cast; ring
  rw [hden,Complex.Gamma_add_one (a+1) ha1,Nat.factorial_succ,pow_succ]
  push_cast
  have hn : (n+1:ℂ)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hnf : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [ha1,hn,hnf]

/-- The genuine derivative of the normalized entire Bessel function is exactly the next normalized order with the printed scalar.
Use: evaluates characteristicSigma' at the original squared zeros using the literal J_(alpha+1), rather than an unspecified slope function.
Article: jacobi, Appendix C.2 (norming ratios).
Source: DLMF 10.6.2, obtained here from the actual convergent spectral series.
Proof: differentiate the already proved genuine analytic power series
at zero. The exact coefficient identity gives the adjacent-order sum
on a neighborhood. Both sides are entire, so the community identity
theorem extends this equality to every complex spectral point. -/
theorem normalized_derivative_order_shift {a : ℂ} (ha : -1<a.re) (z : ℂ) :
    deriv (normalized a) z=(-1/(4*(a+1)))*normalized (a+1) z := by
  -- The local comparison concerns convergent derivative series; the final extension concerns the actual entire functions.
  have hd := scalar_derivative_series (normalized_powerSeries a)
  have hs := normalized_powerSeries (a+1)
  rw [hasFPowerSeriesAt_iff] at hd hs
  have hnear : ∀ᶠ w : ℂ in 𝓝 0,
      deriv (normalized a) w-(-1/(4*(a+1)))*normalized (a+1) w=0 := by
    filter_upwards [hd,hs] with w hw hv
    simp only [coeff_ofScalars,smul_eq_mul,zero_add] at hw hv
    have he : deriv (normalized a) w=(-1/(4*(a+1)))*normalized (a+1) w := by
      have ht := hv.mul_left (-1/(4*(a+1)))
      apply hw.unique
      convert ht using 1
      funext n
      rw [coefficient_order_shift ha]
      ring
    exact sub_eq_zero.mpr he
  have he : AnalyticOnNhd ℂ
      (fun w => deriv (normalized a) w-(-1/(4*(a+1)))*normalized (a+1) w) univ := by
    intro w _
    exact (normalized_analytic a w).deriv.sub
      (analyticAt_const.mul (normalized_analytic (a+1) w))
  exact sub_eq_zero.mp (he.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ 0) hnear (mem_univ z))

end
end jacobi.Bessel

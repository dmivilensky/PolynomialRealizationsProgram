import jacobi.Hankel.ZeroExpansion
import jacobi.Reference.Parameters

/-!
Article: jacobi, Lemma C.1.
Use: the squared genuine Bessel branches have a uniform inverse-square error relative to this same original reference sequence.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal complex polynomial continuation of the original reference spectrum tau.
Use: the squared genuine Bessel branches have a uniform inverse-square error relative to this same original reference sequence.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def frequencyReference (a : ℂ) (k : ℕ) : ℂ := frequencyGrid a k^2+besselCoefficient a

/-- The genuine complex reference spectrum restricts exactly to the earlier original real reference eigenvalues.
Use: the complex zero-tail perturbation has the same tau as the original real GL construction.
Article: jacobi, Lemma E.1.
Proof: substitute the actual affine grid, quadratic coefficient and original real reference eigenvalue; the real inclusion preserves all displayed field operations. -/
theorem frequencyReference_ofReal (a : ℝ) (k : ℕ) :
    frequencyReference (a:ℂ) k=(jacobi.Reference.eigenvalue a k:ℂ) := by
  simp only [frequencyReference,frequencyGrid,besselCoefficient,jacobi.Reference.eigenvalue,
    jacobi.Reference.gamma,jacobi.Jacobi.endpointCorrection]
  push_cast
  ring

/-- The actual original affine frequency grid has an explicit linear norm bound uniform on the complex unit order disk and every positive Lean index.
Use: squared_grid_error turns the genuine cubic frequency remainder into the original inverse-square squared-zero remainder.
Article: jacobi, Lemma E.1.
Proof: bound the original order by the norm of its real center plus one, then apply the complex norm triangle inequality to the actual affine grid. -/
theorem frequencyGrid_upper {a a0 : ℂ} (ha : ‖a-a0‖≤1) {k : ℕ} (hk : 1≤(k:ℝ)) :
    ‖frequencyGrid a k‖≤(Real.pi*(1+(‖a0‖+1)/2+3/4))*(k:ℝ) := by
  -- The coefficient bound is independent of the spectral index throughout the original unit order disk.
  have hn : ‖a‖≤‖a0‖+1 := by have hh := norm_le_norm_sub_add a a0; linarith
  have hsum := (norm_add_le ((k:ℂ)+a/2) (3/4:ℂ)).trans
    (add_le_add (norm_add_le (k:ℂ) (a/2)) le_rfl)
  rw [norm_div] at hsum
  norm_num at hsum
  rw [frequencyGrid,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hinside : ‖(k:ℂ)+a/2+3/4‖≤(1+(‖a0‖+1)/2+3/4)*(k:ℝ) := by
    nlinarith [norm_nonneg a0]
  exact (mul_le_mul_of_nonneg_left hinside Real.pi_pos.le).trans_eq (by ring)

/-- A genuine cubic reciprocal-grid frequency correction yields a uniform inverse-square squared-frequency error relative to the original reference polynomial.
Use: the actual complex Bessel branches satisfy Lemma E.1 after their independently proved frequency estimate is supplied.
Article: jacobi, Lemma E.1.
Proof: first bound the actual displacement by (C+B/2)/x. The exact squared error is 2*q times the genuine cubic correction plus the displacement square. The actual grid norm is at most Q*x, so both terms have inverse-square order. -/
theorem squared_grid_error {c q ζ : ℂ} {B C Q x : ℝ} (hC : 0≤C)
    (hc : ‖c‖≤B) (hx : 1≤x) (hq : x≤‖q‖) (hQ : ‖q‖≤Q*x)
    (he : ‖ζ-c/(2*q)‖≤C/x^3) :
    ‖(q+ζ)^2-(q^2+c)‖≤(2*Q*C+(C+B/2)^2)/x^2 := by
  -- The source reference polynomial is exact; only its genuine frequency correction is estimated.
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hq0 : q≠0 := norm_pos_iff.mp (hxp.trans_le hq)
  have hcoef := frequency_quotient_power_bound hc hxp hq (by norm_num : (0:ℝ)<2) 1
  simp only [pow_one] at hcoef
  have hcubic : C/x^3≤C/x := div_le_div_of_nonneg_left hC hxp (le_self_pow₀ hx (by norm_num : (3:ℕ)≠0))
  have hzeta : ‖ζ‖≤(C+B/2)/x :=
    ((norm_le_norm_sub_add ζ (c/(2*q))).trans (add_le_add (he.trans hcubic) hcoef)).trans_eq (by ring)
  have hident : (q+ζ)^2-(q^2+c)=(2*q)*(ζ-c/(2*q))+ζ^2 := by field_simp; ring
  rw [hident]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul,norm_pow]
  norm_num only [Complex.norm_ofNat]
  have hlead : 2*‖q‖*‖ζ-c/(2*q)‖≤2*(Q*x)*(C/x^3) := mul_le_mul
    (mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ)≤2)) he (norm_nonneg _) (mul_nonneg (by norm_num) ((norm_nonneg q).trans hQ))
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hzeta 2
  exact (add_le_add hlead hsquare).trans_eq (by field_simp)

end
end jacobi.Hankel

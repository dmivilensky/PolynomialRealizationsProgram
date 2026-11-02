import jacobi.Hankel.Operator

/-!
Article: jacobi, Lemma E.1.
Use: the true Jost amplitude tends uniformly to one, and the local inverse estimate preserves the cubic spatial remainder of the explicit asymptotic approximation.
-/
namespace jacobi.Hankel
noncomputable section
open Real Set Filter MeasureTheory

/-- The actual outgoing inverse-square integral at x is bounded by the genuine amplitude bound on its future ray times 1/x.
Use: the true Jost amplitude tends uniformly to one, and the local inverse estimate preserves the cubic spatial remainder of the explicit asymptotic approximation.
Article: jacobi, Lemma E.1.
Proof: below the original Volterra diagonal the actual kernel vanishes. Above it, the two inverse-square cutoffs agree and the original kernel norm is at most one. Integrate the true pointwise majorant and evaluate the genuine tail mass exactly. -/
theorem outgoingIntegral_ray_bound {R x G : ℝ} (hR : 0<R) (hx : R≤x) (hG : 0≤G)
    (f : OutgoingSpace) (hf : ∀ y : ℝ,x<y → ‖f y‖≤G) :
    ‖outgoingIntegral (inverseSquare R) f x‖≤G/x := by
  -- No original low spatial part is bounded crudely: its contribution vanishes by the literal causal kernel.
  have hxp : 0<x := hR.trans_le hx
  have hi := outgoingIntegrand_integrable (inverseSquare_integrable hR) f x
  have hmaj := (inverseSquare_integrable hxp).mul_const G
  have hbound (y : ℝ) : ‖outgoingKernel (y-x)*((inverseSquare R y:ℂ)*f y)‖ ≤ inverseSquare x y*G := by
    by_cases hy : x<y
    · have hRy : R<y := hx.trans_lt hy
      have he : inverseSquare R y=inverseSquare x y := by
        simp only [inverseSquare,indicator_of_mem (show y∈Ioi R from hRy),
          indicator_of_mem (show y∈Ioi x from hy)]
      rw [he,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (inverseSquare_nonneg hxp y)]
      exact (mul_le_of_le_one_left (mul_nonneg (inverseSquare_nonneg hxp y) (norm_nonneg _))
        (outgoingKernel_norm_le _)).trans
          (mul_le_mul_of_nonneg_left (hf y hy) (inverseSquare_nonneg hxp y))
    · rw [outgoingKernel_zero (sub_nonpos.mpr (not_lt.mp hy)),zero_mul,norm_zero]
      exact mul_nonneg (inverseSquare_nonneg hxp y) hG
  have hb := (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hi.norm hmaj (Eventually.of_forall hbound))
  rw [integral_mul_const,inverseSquare_integral hxp] at hb
  exact hb.trans_eq (by ring)

end
end jacobi.Hankel

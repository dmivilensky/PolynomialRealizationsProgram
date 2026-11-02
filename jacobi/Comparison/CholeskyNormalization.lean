import jacobi.Comparison.CholeskyBounds

/-!
Article: jacobi, Proposition C.3.
The true positive Schur normalizations approach one on every cofinal
moving physical row. Their actual inverse square roots therefore
contribute exactly one to the original eigenvector limit.
Use: the genuine target/support polynomial transformation has no extra normalization factor in its continuum Cholesky and eigenvector limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter
open scoped Topology

/-- The actual original Schur normalizations approach one along every
cofinal sequence of actual physical half-chain rows.
Use: the genuine target/support polynomial transformation has no extra
normalization factor in its continuum Cholesky and eigenvector limit.
Article: jacobi, Proposition C.3.
Proof: the original uniform error is bounded by K/N. The true matrix
dimensions tend to infinity, so this common bound vanishes along every
admissible original moving row, including either physical endpoint. -/
theorem rowNormalization_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    (hi:∀ᶠ r:ℕ in atTop,2*(i r).val≤ns r+1) :
    Tendsto (fun r => rowNormalization a b ha hb (ns r) (i r)) atTop (𝓝 1) := by
  -- The genuine uniform error is squeezed by the same K/N on every cofinal moving row.
  obtain ⟨K,_,hbound⟩ := cholesky_uniform_bounds ha hb
  have hN : Tendsto (fun r:ℕ => (ns r:ℝ)+1) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop).comp hns
  have hsmall : Tendsto (fun r:ℕ => K/((ns r:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have herror : Tendsto (fun r => rowNormalization a b ha hb (ns r) (i r)-1) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hsmall
    filter_upwards [hns.eventually hbound,hi] with r hr hir
    rw [Real.norm_eq_abs]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(ns r:ℝ)+1)).mpr
    nlinarith [(hr (i r) hir).2.2]
  simpa only [sub_add_cancel,zero_add] using herror.add_const 1

/-- The genuine inverse positive Schur square root approaches exactly
one on every cofinal moving original physical half-chain row.
Use: Appendix C.4 inserts the actual Schur row formula
without an assumed limiting normalization constant.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: compose the proved genuine normalization limit with continuous
real square root and inversion at its nonzero limit one. -/
theorem rowNormalization_inverse_sqrt_tendsto {a b:ℝ} (ha:-1<a) (hb:-1<b)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i:∀r:ℕ,Fin (ns r+1))
    (hi:∀ᶠ r:ℕ in atTop,2*(i r).val≤ns r+1) :
    Tendsto (fun r => (sqrt (rowNormalization a b ha hb (ns r) (i r)))⁻¹) atTop (𝓝 1) := by
  have hh := ((rowNormalization_tendsto ha hb ns hns i hi).sqrt).inv₀
    (by norm_num : sqrt (1:ℝ)≠0)
  simpa only [sqrt_one,inv_one] using hh

end
end jacobi.Comparison

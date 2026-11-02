import jacobi.GelfandLevitan.FiniteCompression

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The inverses of the actual finite spectral GL compressions converge in
operator norm uniformly over all physical endpoints. The exact inverse
identity, the proved common bounds and the genuine original spectral
tail discharge every approximation premise used here.
Use: the actual finite inverse convergence is in the same original operator norm as kernelOperator_limit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteCompressedPositive compressedPositive kernelOperator

/-- The existing original operator-norm structure, cached through the supported Hilbert subtype.
Use: the actual finite inverse convergence is in the same original operator norm as kernelOperator_limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- The actual finite compressed inverse and original compressed inverse satisfy their exact original resolvent difference identity whenever the finite compression is a genuine unit.
Use: finiteCompressedInverse_error bounds their actual difference and finiteCompressedInverse_uniform_limit discharges this finite-unit condition eventually for every endpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the original operator products and apply the independently proved actual right inverse of A_t and the genuine left inverse of the finite compression.
Source: the elementary inverse difference identity in a noncommutative ring. -/
theorem finiteCompressedInverse_difference (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ)
    (hN : IsUnit (finiteCompressedPositive a ha N t)) :
    finiteCompressedInverse a ha N t-compressedInverse a ha t=
      finiteCompressedInverse a ha N t*(compressedPositive a ha t-finiteCompressedPositive a ha N t)*compressedInverse a ha t := by
  -- Evaluate the genuine original linear maps, so both cancellations use their actual inverse identities on the original Hilbert input.
  apply ContinuousLinearMap.ext
  intro v
  change finiteCompressedInverse a ha N t v-compressedInverse a ha t v=
    finiteCompressedInverse a ha N t
      ((compressedPositive a ha t-finiteCompressedPositive a ha N t) (compressedInverse a ha t v))
  rw [sub_apply,map_sub,compressedPositive_inverse_apply]
  have hi : finiteCompressedInverse a ha N t*finiteCompressedPositive a ha N t=1 := Ring.inverse_mul_cancel _ hN
  have hh := congrArg (fun T : halfSubspace →L[ℝ] halfSubspace => T (compressedInverse a ha t v)) hi
  change finiteCompressedInverse a ha N t (finiteCompressedPositive a ha N t (compressedInverse a ha t v))=
    compressedInverse a ha t v at hh
  rw [hh]

/-- The genuine finite inverse error is bounded by the actual spectral operator tail times the norms of the same two original inverses.
Use: the independently proved actual uniform inverse bounds give finiteCompressedInverse_uniform_limit, needed for the genuine finite GL row limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: use the exact original inverse difference identity, submultiplicativity of the original operator norm and the proved norm-one physical compression estimate. -/
theorem finiteCompressedInverse_error (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ)
    (hN : IsUnit (finiteCompressedPositive a ha N t)) :
    ‖finiteCompressedInverse a ha N t-compressedInverse a ha t‖≤
      ‖finiteCompressedInverse a ha N t‖*‖finiteKernelOperator a ha N-kernelOperator a ha‖*‖compressedInverse a ha t‖ := by
  -- The same original finite compression occurs in the actual inverse identity and in the physical cutoff contraction bound.
  rw [finiteCompressedInverse_difference a ha N t hN]
  have hA : ‖compressedPositive a ha t-finiteCompressedPositive a ha N t‖≤
      ‖finiteKernelOperator a ha N-kernelOperator a ha‖ := by
    rw [norm_sub_rev]
    exact finiteCompressedPositive_error a ha N t
  calc
    _ ≤ (‖finiteCompressedInverse a ha N t‖*‖compressedPositive a ha t-finiteCompressedPositive a ha N t‖)*‖compressedInverse a ha t‖ :=
      (norm_mul_le (finiteCompressedInverse a ha N t*(compressedPositive a ha t-finiteCompressedPositive a ha N t))
        (compressedInverse a ha t)).trans (mul_le_mul_of_nonneg_right
          (norm_mul_le (finiteCompressedInverse a ha N t) (compressedPositive a ha t-finiteCompressedPositive a ha N t))
          (norm_nonneg (compressedInverse a ha t)))
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) (norm_nonneg _)

/-- The actual finite spectral GL inverse family converges to the actual original inverse uniformly in every physical endpoint, in the genuine operator norm.
Use: finite inverse rows and finite reconstructed K converge to their original counterparts without any additional stability, invertibility or numerical certificate premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: original spectral operator tails tend to zero in norm. The original inverse family has a proved common norm bound; sufficiently long actual finite prefixes have proved units and another common inverse bound. Their exact original inverse difference identity makes the actual error uniformly small.
-/
theorem finiteCompressedInverse_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (finiteCompressedInverse a ha) (compressedInverse a ha) atTop := by
  -- The single spectral tail controls the actual inverse error for all physical endpoints at once.
  obtain ⟨B,hB,hFinite⟩ := finiteCompressedPositive_isUnit a ha
  obtain ⟨C,hC,hOriginal⟩ := compressedInverse_uniform_bound a ha
  have he : Tendsto (fun N => ‖finiteKernelOperator a ha N-kernelOperator a ha‖*(B*C)) atTop (𝓝 (0:ℝ)) := by
    simpa only [finiteKernelOperator,sub_self,norm_zero,zero_mul] using
      (((kernelOperator_limit a ha).sub (tendsto_const_nhds (x := kernelOperator a ha))).norm.mul_const (B*C))
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hFinite,(tendsto_order.mp he).2 ε hε] with N hN hsmall t
  rw [dist_eq_norm,norm_sub_rev]
  calc
    _ ≤ ‖finiteCompressedInverse a ha N t‖*‖finiteKernelOperator a ha N-kernelOperator a ha‖*‖compressedInverse a ha t‖ :=
      finiteCompressedInverse_error a ha N t (hN t).1
    _ ≤ B*‖finiteKernelOperator a ha N-kernelOperator a ha‖*C := by
      gcongr
      · exact (hN t).2
      · exact hOriginal t
    _ = ‖finiteKernelOperator a ha N-kernelOperator a ha‖*(B*C) := by ring
    _ < ε := hsmall

end
end jacobi.GelfandLevitan

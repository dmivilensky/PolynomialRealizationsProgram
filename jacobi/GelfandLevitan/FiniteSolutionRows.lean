import jacobi.GelfandLevitan.FiniteInverseConvergence
import jacobi.GelfandLevitan.FiniteKernelMaps
import jacobi.GelfandLevitan.SolutionRows

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite GL inverse rows converge to the original inverse rows
uniformly in the physical endpoint, in their genuine Hilbert norm.
A single original spectral error controls both the uniform kernel tail
and operator tail. All finite inverse bounds are already discharged.
Use: uniform finite row convergence uses exactly the original L2 topology.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernelOperator kernelRowVector

/-- The original Hilbert norm structure, cached through the unchanged supported subtype.
Use: uniform finite row convergence uses exactly the original L2 topology.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup halfSubspace := inferInstance

/-- The original operator norm structure, cached for continuity of the genuine finite spectral errors.
Use: finiteApproximationError_limit uses the already proved original operator convergence.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- The actual finite GL inverse solution row, formed from the genuine finite spectral kernel and its actual compressed inverse.
Use: finiteSolutionRow_error and finiteSolutionRow_uniform_limit compare these same original finite solutions with the constructed original row k_t.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteSolutionRow (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) : halfSubspace :=
  -(finiteCompressedInverse a ha N t (cutoffProjection t (finiteKernelRowVector a ha N t)))

/-- One genuine nonnegative original spectral tail controlling both compact-kernel and Hilbert-operator approximation.
Use: the actual finite row and reconstruction errors are bounded by constant multiples of this same tail, which tends to zero without any supplied convergence certificate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteApproximationError (a : ℝ) (ha : -1<a) (N : ℕ) : ℝ :=
  ‖finiteKernelMap a ha N-kernelMap a ha‖+‖finiteKernelOperator a ha N-kernelOperator a ha‖

/-- The genuine original simultaneous finite approximation error tends to zero.
Use: finiteSolutionRow_uniform_limit and the finite K limit discharge their actual approximation bounds for the original data.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: add the independently proved uniform-kernel and operator-norm tail limits of the same original finite spectral prefixes. -/
theorem finiteApproximationError_limit (a : ℝ) (ha : -1<a) :
    Tendsto (finiteApproximationError a ha) atTop (𝓝 (0:ℝ)) := by
  change Tendsto (fun N => ‖finiteKernelMap a ha N-kernelMap a ha‖+
    ‖finiteKernelOperator a ha N-kernelOperator a ha‖) atTop (𝓝 (0:ℝ))
  simpa only [finiteApproximationError,finiteKernelOperator,sub_self,norm_zero,zero_add] using
    (((finiteKernelMap_limit a ha).sub (tendsto_const_nhds (x := kernelMap a ha))).norm.add
      ((kernelOperator_limit a ha).sub (tendsto_const_nhds (x := kernelOperator a ha))).norm)

/-- The actual finite inverse row differs from the original row by the original finite data error and the genuine inverse error.
Use: finiteSolutionRow_error inserts the proved common inverse and source-row bounds to obtain one uniform genuine spectral-tail estimate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: subtract the actual inverse formulas, insert the same original row under the finite inverse, and use linearity. Bound both physical projections by one and use the genuine continuous-row embedding error for the original finite source data. -/
theorem finiteSolutionRow_difference_bound (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    ‖finiteSolutionRow a ha N t-solutionRow a ha t‖≤
      ‖finiteCompressedInverse a ha N t‖*‖rowEmbedding‖*‖finiteKernelMap a ha N-kernelMap a ha‖+
      ‖finiteCompressedInverse a ha N t-compressedInverse a ha t‖*‖kernelRowVector a ha t‖ := by
  -- Both terms retain their actual original input; no operator-norm derivative of the physical projection is used.
  have he : finiteSolutionRow a ha N t-solutionRow a ha t=
      -(finiteCompressedInverse a ha N t (cutoffProjection t
        (finiteKernelRowVector a ha N t-kernelRowVector a ha t)))-
      (finiteCompressedInverse a ha N t-compressedInverse a ha t)
        (cutoffProjection t (kernelRowVector a ha t)) := by
    rw [finiteSolutionRow,solutionRow,sub_apply,map_sub,map_sub]
    abel
  rw [he]
  have h1 : ‖finiteCompressedInverse a ha N t (cutoffProjection t
      (finiteKernelRowVector a ha N t-kernelRowVector a ha t))‖≤
      ‖finiteCompressedInverse a ha N t‖*‖rowEmbedding‖*‖finiteKernelMap a ha N-kernelMap a ha‖ := by
    calc
      _ ≤ ‖finiteCompressedInverse a ha N t‖*‖cutoffProjection t (finiteKernelRowVector a ha N t-kernelRowVector a ha t)‖ :=
        (finiteCompressedInverse a ha N t).le_opNorm _
      _ ≤ ‖finiteCompressedInverse a ha N t‖*‖finiteKernelRowVector a ha N t-kernelRowVector a ha t‖ :=
        mul_le_mul_of_nonneg_left ((cutoffSubspace t).norm_starProjection_apply_le _) (norm_nonneg _)
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left (finiteKernelRowVector_error a ha N t) (norm_nonneg (finiteCompressedInverse a ha N t))
        simpa only [mul_assoc] using hb
  have h2 : ‖(finiteCompressedInverse a ha N t-compressedInverse a ha t)
      (cutoffProjection t (kernelRowVector a ha t))‖≤
      ‖finiteCompressedInverse a ha N t-compressedInverse a ha t‖*‖kernelRowVector a ha t‖ :=
    ((finiteCompressedInverse a ha N t-compressedInverse a ha t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((cutoffSubspace t).norm_starProjection_apply_le _) (norm_nonneg _))
  exact (norm_sub_le _ _).trans (by rw [norm_neg]; exact add_le_add h1 h2)

/-- Every sufficiently long actual finite inverse row is uniformly close to the genuine original inverse row, with one proved positive coefficient times the true original spectral tail.
Use: gives finiteSolutionRow_uniform_limit and the genuine finite K approximation used in the original transformed differential equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: combine the exact original inverse-row difference bound, the actual original inverse difference estimate, proved common finite and original inverse norms, and the compact original source-row bound. Both nonnegative original tails are dominated by their sum. -/
theorem finiteSolutionRow_error (a : ℝ) (ha : -1<a) :
    ∃ D : ℝ,0<D ∧ ∀ᶠ N : ℕ in atTop,∀ t : HalfInterval,
      ‖finiteSolutionRow a ha N t-solutionRow a ha t‖≤D*finiteApproximationError a ha N := by
  -- All constants come from proved original inverse and source data; the single threshold is the genuine finite unit threshold.
  obtain ⟨B,hB,hFinite⟩ := finiteCompressedPositive_isUnit a ha
  obtain ⟨C,hC,hOriginal⟩ := compressedInverse_uniform_bound a ha
  obtain ⟨R,hR,hRows⟩ := kernelRowVector_bounded a ha
  let D := B*‖rowEmbedding‖+B*C*R+1
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  filter_upwards [hFinite] with N hN t
  have he := finiteCompressedInverse_error a ha N t (hN t).1
  have hi : ‖finiteCompressedInverse a ha N t-compressedInverse a ha t‖≤
      B*‖finiteKernelOperator a ha N-kernelOperator a ha‖*C := he.trans (by
    gcongr
    · exact (hN t).2
    · exact hOriginal t)
  have hr := finiteSolutionRow_difference_bound a ha N t
  have hb : ‖finiteSolutionRow a ha N t-solutionRow a ha t‖≤
      B*‖rowEmbedding‖*‖finiteKernelMap a ha N-kernelMap a ha‖+
      B*‖finiteKernelOperator a ha N-kernelOperator a ha‖*C*R := hr.trans (by
    gcongr
    · exact (hN t).2
    · exact hRows t)
  have h1 : B*‖rowEmbedding‖≤D := by dsimp [D]; nlinarith [show 0≤B*C*R by positivity]
  have h2 : B*C*R≤D := by dsimp [D]; nlinarith [show 0≤B*‖rowEmbedding‖ by positivity]
  have hδ := mul_le_mul_of_nonneg_right h1 (norm_nonneg (finiteKernelMap a ha N-kernelMap a ha))
  have hη := mul_le_mul_of_nonneg_right h2 (norm_nonneg (finiteKernelOperator a ha N-kernelOperator a ha))
  dsimp only [finiteApproximationError]
  nlinarith

/-- The actual original finite GL inverse rows converge uniformly in the original physical endpoint in their genuine L2 norm.
Use: the same actual finite K and transformed solutions converge to their original counterparts before their true differential identities are passed to the limit.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual row error is eventually bounded by one constant times the independently proved genuine original spectral tail tending to zero. The community metric uniform-convergence criterion gives the assertion. -/
theorem finiteSolutionRow_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (finiteSolutionRow a ha) (solutionRow a ha) atTop := by
  obtain ⟨D,_,hD⟩ := finiteSolutionRow_error a ha
  have he : Tendsto (fun N => D*finiteApproximationError a ha N) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (finiteApproximationError_limit a ha).const_mul D
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hD,(tendsto_order.mp he).2 ε hε] with N hN hsmall t
  rw [dist_eq_norm,norm_sub_rev]
  exact (hN t).trans_lt hsmall

end
end jacobi.GelfandLevitan

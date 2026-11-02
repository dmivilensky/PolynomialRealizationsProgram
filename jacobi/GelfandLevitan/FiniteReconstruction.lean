import jacobi.GelfandLevitan.FiniteSolutionRows
import jacobi.GelfandLevitan.Reconstruction

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The genuine finite inverse rows reconstruct the actual finite kernels
K^(N). These converge uniformly to the original K on the entire original
half square. The proof uses the true original row and inverse errors;
no finite approximation or stability certificate is assumed.
Use: the genuine uniform finite inverse-row bound uses the original source L2 norm.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel kernelRowVector

/-- The original Hilbert norm structure, cached through the unchanged physical support subtype.
Use: the genuine uniform finite inverse-row bound uses the original source L2 norm.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup halfSubspace := inferInstance

/-- The unchanged original operator norm structure, cached through the physical support subtype.
Use: nonnegative genuine spectral operator tails enter the actual finite kernel error bound.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance : SeminormedAddCommGroup (halfSubspace →L[ℝ] halfSubspace) := inferInstance

/-- The actual finite GL kernel reconstructed from the original finite spectral source and its genuine finite inverse row.
Use: finiteTransformationKernel_uniform_limit proves convergence to the original constructed K; the separate finite GL identity identifies this reconstruction with the article's finite transformation kernel.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformationKernel (a : ℝ) (ha : -1<a) (N : ℕ) (t s : HalfInterval) : ℝ :=
  -finiteKernelRows a ha N t (halfInclusion s)-inner ℝ (finiteKernelRowVector a ha N s) (finiteSolutionRow a ha N t)

/-- The actual original K is the identical continuous-source-row reconstruction used for its genuine finite approximations.
Use: subtracts the original finite and infinite formulas in finiteTransformationKernel_error, retaining precisely the same physical coordinates and Hilbert pairings.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the unchanged original source row at its actual physical point; its half-coordinate clamp fixes that point. -/
theorem transformationKernel_row_formula (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    transformationKernel a ha t s= -kernelRows a ha t (halfInclusion s)-
      inner ℝ (kernelRowVector a ha s) (solutionRow a ha t) := by
  rw [transformationKernel,kernelRows_apply]
  change -kernel a ha t s-_= -kernel a ha t (min (s:ℝ) (1/2))-_
  rw [min_eq_left s.property.2]

/-- The genuine original finite inverse rows have one common positive Hilbert norm bound for every physical endpoint once the prefix is sufficiently long.
Use: the actual finite transformation kernel error is controlled by the original source-row error and inverse-row convergence.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original inverse rows are uniformly bounded, and the genuine finite rows converge uniformly to them in the original Hilbert norm. The original triangle inequality gives one common bound. -/
theorem finiteSolutionRow_uniform_bound (a : ℝ) (ha : -1<a) :
    ∃ Q : ℝ,0<Q ∧ ∀ᶠ N : ℕ in atTop,∀ t : HalfInterval,‖finiteSolutionRow a ha N t‖≤Q := by
  obtain ⟨Q,hQ,hRows⟩ := solutionRow_bounded a ha
  refine ⟨Q+1,by positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformly_iff.mp (finiteSolutionRow_uniform_limit a ha)) 1 zero_lt_one] with N hN t
  have he : ‖finiteSolutionRow a ha N t-solutionRow a ha t‖<1 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hN t
  exact (norm_le_norm_sub_add (finiteSolutionRow a ha N t) (solutionRow a ha t)).trans (by linarith [hRows t])

/-- The actual finite original transformation kernels have one uniform positive multiple of the true original spectral tail as their full physical-square error bound.
Use: finiteTransformationKernel_uniform_limit discharges the genuine finite-kernel convergence in the original differential-equation approximation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: subtract the identical actual reconstruction formulas. The source error is bounded in uniform norm, the true source-row error is paired with a uniformly bounded actual finite inverse row, and the true inverse-row error is paired with a bounded original source row. All three bounds use the same genuine original spectral tail. -/
theorem finiteTransformationKernel_error (a : ℝ) (ha : -1<a) :
    ∃ L : ℝ,0<L ∧ ∀ᶠ N : ℕ in atTop,∀ t s : HalfInterval,
      ‖finiteTransformationKernel a ha N t s-transformationKernel a ha t s‖≤L*finiteApproximationError a ha N := by
  -- The error identity uses the original finite and infinite Hilbert rows, so every estimate compares actual source data in the same genuine space.
  obtain ⟨Q,hQ,hFinite⟩ := finiteSolutionRow_uniform_bound a ha
  obtain ⟨R,hR,hRows⟩ := kernelRowVector_bounded a ha
  obtain ⟨D,hD,hError⟩ := finiteSolutionRow_error a ha
  let L := 1+‖rowEmbedding‖*Q+R*D
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  filter_upwards [hFinite,hError] with N hN he t s
  have herr0 : 0≤finiteApproximationError a ha N := by unfold finiteApproximationError; positivity
  have hδ : ‖finiteKernelMap a ha N-kernelMap a ha‖≤finiteApproximationError a ha N :=
    le_add_of_nonneg_right (norm_nonneg (finiteKernelOperator a ha N-kernelOperator a ha))
  have hsource : ‖finiteKernelRows a ha N t (halfInclusion s)-kernelRows a ha t (halfInclusion s)‖≤
      finiteApproximationError a ha N :=
    (((finiteKernelRows a ha N t-kernelRows a ha t).norm_coe_le_norm (halfInclusion s)).trans
      (finiteKernelRows_error a ha N t)).trans hδ
  have hrow : ‖finiteKernelRowVector a ha N s-kernelRowVector a ha s‖≤‖rowEmbedding‖*finiteApproximationError a ha N :=
    (finiteKernelRowVector_error a ha N s).trans (mul_le_mul_of_nonneg_left hδ (norm_nonneg rowEmbedding))
  have hfirst : ‖inner ℝ (finiteKernelRowVector a ha N s-kernelRowVector a ha s) (finiteSolutionRow a ha N t)‖≤
      (‖rowEmbedding‖*finiteApproximationError a ha N)*Q :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hrow (hN t) (norm_nonneg _) (by positivity))
  have hsecond : ‖inner ℝ (kernelRowVector a ha s) (finiteSolutionRow a ha N t-solutionRow a ha t)‖≤
      R*(D*finiteApproximationError a ha N) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hRows s) (he t) (norm_nonneg _) hR.le)
  have hid : finiteTransformationKernel a ha N t s-transformationKernel a ha t s=
      -(finiteKernelRows a ha N t (halfInclusion s)-kernelRows a ha t (halfInclusion s))-
      inner ℝ (finiteKernelRowVector a ha N s-kernelRowVector a ha s) (finiteSolutionRow a ha N t)-
      inner ℝ (kernelRowVector a ha s) (finiteSolutionRow a ha N t-solutionRow a ha t) := by
    rw [finiteTransformationKernel,transformationKernel_row_formula,inner_sub_left,inner_sub_right]
    ring
  rw [hid]
  calc
    _ ≤ (‖-(finiteKernelRows a ha N t (halfInclusion s)-kernelRows a ha t (halfInclusion s))‖+
      ‖inner ℝ (finiteKernelRowVector a ha N s-kernelRowVector a ha s) (finiteSolutionRow a ha N t)‖)+
      ‖inner ℝ (kernelRowVector a ha s) (finiteSolutionRow a ha N t-solutionRow a ha t)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (finiteApproximationError a ha N+(‖rowEmbedding‖*finiteApproximationError a ha N)*Q)+
      R*(D*finiteApproximationError a ha N) := by rw [norm_neg]; exact add_le_add (add_le_add hsource hfirst) hsecond
    _ = _ := by dsimp [L]; ring

/-- The actual finite spectral GL transformation kernels converge uniformly to the original K on its entire genuine half square.
Use: the actual finite diagonals and transformed solutions converge before their original differential identities are passed to the limit in Proposition C.2.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine full-square error is bounded eventually by a fixed constant times the actual original spectral tail tending to zero. Apply the community metric uniform-convergence criterion. -/
theorem finiteTransformationKernel_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformly (fun (N : ℕ) (p : HalfInterval×HalfInterval) => finiteTransformationKernel a ha N p.1 p.2)
      (fun p : HalfInterval×HalfInterval => transformationKernel a ha p.1 p.2) atTop := by
  obtain ⟨L,_,hL⟩ := finiteTransformationKernel_error a ha
  have he : Tendsto (fun N => L*finiteApproximationError a ha N) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (finiteApproximationError_limit a ha).const_mul L
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [hL,(tendsto_order.mp he).2 ε hε] with N hN hsmall p
  rw [dist_eq_norm,norm_sub_rev]
  exact (hN p.1 p.2).trans_lt hsmall

end
end jacobi.GelfandLevitan

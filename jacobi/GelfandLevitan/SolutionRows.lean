import jacobi.GelfandLevitan.KernelRows
import jacobi.GelfandLevitan.Compression

/-!
Article: jacobi, Proposition C.2.
The original right-hand side is projected onto the physical interval
and acted on by its proved bounded inverse. These actual vectors solve
the source equation uniquely, vanish beyond the physical endpoint and
have one common bound, including at the singular left endpoint.
Use: constructs the original pointwise GL kernel by the source row integral, without postulating a solution of the integral equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace

/-- The actual inverse solution row on the fixed original half-interval Hilbert space.
Use: constructs the original pointwise GL kernel by the source row integral, without postulating a solution of the integral equation.
Article: jacobi, Proposition C.2.
-/
def solutionRow (a : ℝ) (ha : -1<a) (t : HalfInterval) : halfSubspace :=
  -(compressedInverse a ha (t:ℝ) (cutoffProjection (t:ℝ) (kernelRowVector a ha t)))

/-- The actual inverse row satisfies the original compressed GL equation.
Use: proves its support, uniqueness and the pointwise GL equation after reconstruction of the continuous kernel.
Article: jacobi, Proposition C.2.
Proof: linearity of the actual compressed operator and its proved right inverse identity evaluate the defining original inverse solution. -/
theorem solutionRow_equation (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    compressedPositive a ha (t:ℝ) (solutionRow a ha t)=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t)) := by
  rw [solutionRow,map_neg,compressedPositive_inverse_apply]

/-- No other original Hilbert vector solves the same compressed GL row equation.
Use: identifies any continuous solution of the original integral equation with the actual inverse row, establishing uniqueness of K.
Article: jacobi, Proposition C.2.
Proof: the original compressed operator is a proved unit and hence injective; compare its actual images. -/
theorem solutionRow_unique (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (v : halfSubspace)
    (hv : compressedPositive a ha (t:ℝ) v=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t))) : v=solutionRow a ha t :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp (compressedPositive_isUnit a ha (t:ℝ))).1
    (hv.trans (solutionRow_equation a ha t).symm)

/-- The original inverse row is fixed by its actual physical cutoff projection.
Use: its original L2 representative vanishes beyond t, so reconstruction integrates over precisely the original source interval.
Article: jacobi, Proposition C.2.
Proof: project the actual compressed equation once more. The source
and both outer kernel terms are already fixed by the genuine idempotent
projection. Subtract the two equalities to identify the original row
with its actual prefix component. -/
theorem solutionRow_projected (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    cutoffProjection (t:ℝ) (solutionRow a ha t)=solutionRow a ha t := by
  -- Every kernel term in the true compressed equation already belongs to the actual prefix space.
  have he := solutionRow_equation a ha t
  change solutionRow a ha t+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (solutionRow a ha t)))=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t)) at he
  have hp := congrArg (cutoffProjection (t:ℝ)) he
  rw [map_add,map_neg,cutoffProjection_idempotent,cutoffProjection_idempotent] at hp
  exact add_right_cancel (hp.trans he.symm)

/-- The true inverse solution belongs to the original interval subspace.
Use: its exact source support is needed when the Hilbert reconstruction is rewritten as the original GL integral on [0,t].
Article: jacobi, Proposition C.4.
Proof: it equals its actual cutoff projection, whose image belongs to the genuine source cutoff domain. -/
theorem solutionRow_mem (a : ℝ) (ha : -1<a) (t : HalfInterval) :
    solutionRow a ha t∈cutoffSubspace (t:ℝ) := by
  rw [← solutionRow_projected a ha t]
  exact cutoffProjection_mem _ _

/-- The original inverse solution rows have one finite positive bound over the entire physical parameter interval.
Use: gives the actual uniform pointwise bound for the reconstructed original GL kernel K.
Article: jacobi, Proposition C.2.
Proof: combine the true uniform compressed inverse bound, the actual
norm-one cutoff estimate and the compact continuous source row bound.
The original solution has only a harmless overall minus sign. -/
theorem solutionRow_bounded (a : ℝ) (ha : -1<a) :
    ∃ B:ℝ,0<B ∧ ∀ t:HalfInterval,‖solutionRow a ha t‖≤B := by
  -- The same true inverse bound and compact source-row bound work at every physical endpoint.
  obtain ⟨C,hC,hInv⟩ := compressedInverse_uniform_bound a ha
  obtain ⟨B,hB,hRow⟩ := kernelRowVector_bounded a ha
  refine ⟨C*B,mul_pos hC hB,fun t => ?_⟩
  rw [solutionRow,norm_neg]
  calc
    _ ≤ ‖compressedInverse a ha (t:ℝ)‖*‖cutoffProjection (t:ℝ) (kernelRowVector a ha t)‖ :=
      (compressedInverse a ha (t:ℝ)).le_opNorm _
    _ ≤ C*‖kernelRowVector a ha t‖ := mul_le_mul
      (hInv _) ((cutoffSubspace (t:ℝ)).norm_starProjection_apply_le _)
      (norm_nonneg _) hC.le
    _ ≤ C*B := mul_le_mul_of_nonneg_left (hRow t) hC.le

/-- The original solution row is zero at the genuine singular endpoint.
Use: fixes the reconstructed original kernel endpoint K(0,s)=0.
Article: jacobi, Proposition C.2.
Proof: the original source row vanishes at zero and the actual cutoff and inverse maps are linear. -/
theorem solutionRow_zero (a : ℝ) (ha : -1<a) : solutionRow a ha halfZero=0 := by
  rw [solutionRow,kernelRowVector_zero,map_zero,map_zero,neg_zero]

end
end jacobi.GelfandLevitan

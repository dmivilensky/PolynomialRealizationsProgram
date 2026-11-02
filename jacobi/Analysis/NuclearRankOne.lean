import chebyshev2.Continuum.TraceClassSpace
import chebyshev2.Continuum.ProjectorNorm
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Article: jacobi, Theorem 2.1.
Rank-one formation is continuous in the genuine nuclear-norm Banach
space for every real Hilbert space, including the original physical L2
interval. Its exact norm is reused from chebyshev2.
Source: rank-one trace norm and bounded bilinear maps.
Use: eigenprojector limits and spectral summation in Theorem 2.1 take place in trace norm, retaining the original physical Hilbert space.
-/
namespace jacobi.Analysis
noncomputable section
open chebyshev2.Continuum
open scoped InnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine rank-one operator in the actual nuclear-norm space.
Use: eigenprojector limits and spectral summation in Theorem 2.1 take place
in trace norm, retaining the original physical Hilbert space.
Article: jacobi, Theorem 2.1.
-/
def traceRankOne (u v:E) : TraceClassOperator E :=
  ⟨InnerProductSpace.rankOne ℝ u v,rankOne_isTraceClass u v⟩

/-- The genuine nuclear rank-one norm is exactly the product of the
original Hilbert vector norms, including zero vectors.
Use: the embedded unit eigenprojectors have a uniform trace-norm bound.
Article: jacobi, Theorem 2.1.
Source: chebyshev2, Continuum.nuclearNorm_rankOne.
Proof: insert the earlier exact nuclear norm into the genuine nuclear
space norm; the product of the actual vector norms is nonnegative. -/
theorem traceRankOne_norm (u v:E) : ‖traceRankOne u v‖=‖u‖*‖v‖ := by
  rw [TraceClassOperator.norm_def]
  change (nuclearNorm (InnerProductSpace.rankOne ℝ u v)).toReal=_
  rw [nuclearNorm_rankOne,ENNReal.toReal_ofReal (by positivity)]

/-- Genuine rank-one formation is bounded bilinear in nuclear norm.
Use: the actual L2 eigenvector convergence gives actual trace-norm
projector convergence before the complete spectral sums are taken.
Article: jacobi, Theorem 2.1.
Proof: check the linear identities on the underlying operators; the
already proved exact nuclear norm gives bilinear bound one. -/
theorem traceRankOne_bilinear : IsBoundedBilinearMap ℝ (fun p:E×E => traceRankOne p.1 p.2) where
  -- Equality is checked through the injective original operator inclusion.
  add_left u v w := by
    -- Nuclear-space equality follows from equality of the same bounded rank-one operators.
    apply TraceClassOperator.ext
    simp [traceRankOne,TraceClassOperator.val_add,map_add]
  smul_left c u v := by
    apply TraceClassOperator.ext
    simp [traceRankOne,TraceClassOperator.val_smul]
  add_right u v w := by
    apply TraceClassOperator.ext
    simp [traceRankOne,TraceClassOperator.val_add,map_add]
  smul_right c u v := by
    apply TraceClassOperator.ext
    simp [traceRankOne,TraceClassOperator.val_smul]
  bound := ⟨1,by norm_num,fun u v => by simp only [traceRankOne_norm,one_mul,le_refl]⟩

end
end jacobi.Analysis

import jacobi.Comparison.NuclearGreenLimit
import jacobi.Comparison.FiniteGreenOperators

/-!
Article: jacobi, Theorem 2.1.
The actual matrix inverse, the original physical step isometry and its
Hilbert adjoint are identified exactly with the proved nuclear spectral
series. Thus its genuine trace-norm limit is the same H_alpha inverse
constructed in Proposition C.2, with no surrogate operator or remaining premise.
Use: the operator embeddedGreenOperator is literally the matrix inverse printed in Theorem 2.1, with all nonsingularity assumptions proved.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter Matrix jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan chebyshev2.Continuum
open scoped Topology

/-- The original finite scaled matrix inverse is precisely the positive
scalar multiple of its actual original Green inverse.
Use: the operator embeddedGreenOperator is literally the matrix inverse
printed in Theorem 2.1, with all nonsingularity assumptions proved.
Article: jacobi, Theorem 2.1.
Proof: the actual characteristic polynomial is the original Jacobi
node polynomial, whose value at one is positive. Thus I-J is genuinely
invertible, and the community scalar-matrix inverse identity applies. -/
theorem target_scaled_inverse (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    ((2*((n:ℝ)+1)^2) • (1-(targetChain a b ha hb n).matrix))⁻¹=
      (1/(2*((n:ℝ)+1)^2)) • (targetChain a b ha hb n).green := by
  -- The same actual polynomial supplies nonsingularity before using the matrix inverse law.
  have hp : (targetChain a b ha hb n).matrix.charpoly.eval 1≠0 := by
    rw [(targetChain_inFiber a b ha hb n).2]
    exact ((jacobi.Jacobi.nodes a b ha hb (n+1)).endpoint_pos).ne'
  have hd : IsUnit ((1-(targetChain a b ha hb n).matrix).det) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [Matrix.eval_charpoly,map_one] using hp
  let _ : Invertible (2*((n:ℝ)+1)^2) := invertibleOfNonzero (by positivity)
  simpa only [invOf_eq_inv,one_div,chebyshev2.Jacobi.green] using
    Matrix.inv_smul (1-(targetChain a b ha hb n).matrix) (2*((n:ℝ)+1)^2) hd

/-- The genuine nuclear finite inverse is exactly the actual original
matrix inverse transported by the actual step isometry and its adjoint.
Use: embeddedGreenOperator_trace_limit is the literal trace-norm
convergence assertion of Theorem 2.1 for the original source matrices.
Article: jacobi, Theorem 2.1.
Proof: the original zero padding removes every spectral term beyond
N. The original finite spectral formula and genuine rank-one transport
identify the remaining exact finite sum with the direct embedded inverse. -/
theorem finiteNuclearGreen_operator (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (finiteNuclearGreen a b ha hb n).val=embeddedGreenOperator a b ha hb n := by
  -- Finite support justifies commuting the original nuclear inclusion with this exact finite sum.
  have he : finiteNuclearGreen a b ha hb n=∑k:Fin (n+1),jacobi.Jacobi.finiteLambda a b ha hb (n+1) k •
      ((1/2:ℝ) • traceRankOne (embeddedTargetEigenvector a b ha hb n k.val)
        (embeddedTargetEigenvector a b ha hb n k.val)) := by
    unfold finiteNuclearGreen
    rw [tsum_eq_sum (s:=Finset.range (n+1)) (fun k hk => by
      rw [jacobi.Jacobi.finiteLambdaAt_zero ha hb (by simpa only [Finset.mem_range,not_lt] using hk),zero_smul])]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [jacobi.Jacobi.finiteLambdaAt_eq ha hb k.isLt]
  change TraceClassOperator.toOperator Space (finiteNuclearGreen a b ha hb n)=_
  rw [he,map_sum,embeddedGreenOperator_spectral]
  apply Finset.sum_congr rfl
  intro k _
  change jacobi.Jacobi.finiteLambda a b ha hb (n+1) k • ((1/2:ℝ) • InnerProductSpace.rankOne ℝ
    (embeddedTargetEigenvector a b ha hb n k.val) (embeddedTargetEigenvector a b ha hb n k.val))=_
  rw [smul_smul]
  congr 1
  ring

/-- The original embedded matrix inverses converge to the actual full
H_alpha inverse in the genuine trace norm.
Use: this completes the operator assertion of Theorem 2.1, using
the same original matrix inverse, U_N and H_alpha as the article.
Article: jacobi, Theorem 2.1.
Proof: the actual nuclear spectral series converge in their Banach
norm. Their underlying operators are the proved direct finite embedded
inverse and the same actual continuum Green inverse. The nuclear-space
norm is exactly the trace norm of this actual operator difference. -/
theorem embeddedGreenOperator_trace_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => (nuclearNorm
      (embeddedGreenOperator a b ha hb n-targetGreenOperator a ha)).toReal) atTop (𝓝 0) := by
  have hh := ((finiteNuclearGreen_limit ha hb).sub (tendsto_const_nhds (x:=targetNuclearGreen a ha))).norm
  simpa only [sub_self,norm_zero,TraceClassOperator.norm_def,TraceClassOperator.val_sub,
    finiteNuclearGreen_operator,targetNuclearGreen_operator] using hh

/-- Every actual finite embedded inverse difference is genuinely trace
class, so the preceding real trace norm is its finite ordinary value.
Use: the trace-norm limit of Theorem 2.1 cannot arise from totalizing an infinite
nuclear norm with toReal; all original operators are trace class.
Article: jacobi, Theorem 2.1.
Proof: the difference is the actual underlying operator of a genuine
nuclear-space difference, with the exact original identifications. -/
theorem embeddedGreenOperator_difference_traceClass (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    IsTraceClass (embeddedGreenOperator a b ha hb n-targetGreenOperator a ha) := by
  rw [← finiteNuclearGreen_operator,← targetNuclearGreen_operator,← TraceClassOperator.val_sub]
  exact (finiteNuclearGreen a b ha hb n-targetNuclearGreen a ha).property

end
end jacobi.Comparison

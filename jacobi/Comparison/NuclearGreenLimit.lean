import jacobi.Comparison.EmbeddedEigenvectorLimit
import jacobi.Comparison.FiniteEigenvectorNorm
import jacobi.Analysis.NuclearRankOne
import jacobi.Analysis.WeightedSeriesNormed
import jacobi.Jacobi.FibreLimit
import jacobi.GelfandLevitan.TargetGreenOperator

/-!
Article: jacobi, Theorem 2.1.
The original embedded finite spectral inverse converges in the genuine
nuclear-norm Banach space to the actual continuum Green inverse. The
finite operator's direct matrix/adjoint identification is supplied by
the separate exact finite spectral transport identity.
Use: finiteNuclearGreen_operator identifies it with the printed direct finite matrix inverse transported by the actual U_N and its adjoint.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan chebyshev2.Continuum
open scoped Topology

/-- The actual finite embedded inverse expressed by its genuine target
spectral vectors in the original nuclear-norm operator space.
Use: finiteNuclearGreen_operator identifies it with the printed direct
finite matrix inverse transported by the actual U_N and its adjoint.
Article: jacobi, Theorem 2.1.
-/
def finiteNuclearGreen (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : TraceClassOperator Space :=
  ∑'k,jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k •
    ((1/2:ℝ) • traceRankOne (embeddedTargetEigenvector a b ha hb n k) (embeddedTargetEigenvector a b ha hb n k))

/-- The actual continuum spectral inverse in the genuine nuclear space.
Use: targetNuclearGreen_operator identifies its underlying operator
with the already proved original Green inverse of the actual H_alpha.
Article: jacobi, Theorem 2.1.
-/
def targetNuclearGreen (a:ℝ) (ha:-1<a) : TraceClassOperator Space :=
  ∑'k,jacobi.Bessel.edgeValue a ha k •
    ((1/2:ℝ) • traceRankOne (fullTargetBasis a ha k:Space) (fullTargetBasis a ha k:Space))

/-- The genuine finite embedded half-projectors have nuclear norm
at most one over the entire original padded spectrum and every dimension.
Use: nuclear spectral summation is dominated by the actual L1 edge
spectrum, retaining trace norm throughout the argument.
Article: jacobi, Theorem 2.1.
Proof: the actual step embedding preserves each finite vector norm,
and the genuine rank-one nuclear norm is the product of those norms. -/
theorem embedded_half_projector_bound (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) :
    ‖(1/2:ℝ) • traceRankOne (embeddedTargetEigenvector a b ha hb n k)
      (embeddedTargetEigenvector a b ha hb n k)‖≤1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),traceRankOne_norm]
  have hv := embeddedTargetEigenvector_norm_le_one a b ha hb n k
  nlinarith [sq_nonneg ‖embeddedTargetEigenvector a b ha hb n k‖,
    mul_le_mul hv hv (norm_nonneg _) (by norm_num : (0:ℝ)≤1)]

/-- The actual continuum nuclear inverse series is genuinely norm
summable before commuting its sum with the original operator inclusion.
Use: targetNuclearGreen_operator identifies precisely the same genuine
nuclear limit with the actual Green operator of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the actual full target basis vectors have norm one. Their
half-projectors have norm 1/2, and the genuine Bessel weights are summable. -/
theorem targetNuclearGreen_summable (a:ℝ) (ha:-1<a) :
    Summable (fun k => jacobi.Bessel.edgeValue a ha k •
      ((1/2:ℝ) • traceRankOne (fullTargetBasis a ha k:Space) (fullTargetBasis a ha k:Space))) := by
  apply (jacobi.Bessel.edgeValue_summable ha).abs.of_norm_bounded
  intro k
  rw [norm_smul,norm_smul,traceRankOne_norm,(fullTargetBasis a ha).orthonormal.norm_eq_one,
    mul_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  nlinarith [abs_nonneg (jacobi.Bessel.edgeValue a ha k)]

/-- The genuine nuclear continuum inverse is exactly the original full
Green operator already proved inverse to H_alpha on its full domain.
Use: the trace-norm finite spectral limit is a limit to the same actual
source operator, not an independently defined spectral candidate.
Article: jacobi, Theorem 2.1.
Proof: continuity of the original nuclear inclusion commutes with the
proved genuine nuclear series; its coefficients are exactly 1/sigma_k. -/
theorem targetNuclearGreen_operator (a:ℝ) (ha:-1<a) :
    (targetNuclearGreen a ha).val=targetGreenOperator a ha := by
  -- Commute the actual nuclear inclusion with the genuinely norm-summable original series.
  have hh := (TraceClassOperator.toOperator Space).map_tsum (targetNuclearGreen_summable a ha)
  change (targetNuclearGreen a ha).val=_ at hh
  rw [hh]
  unfold targetGreenOperator diagonalOperator
  apply tsum_congr
  intro k
  change jacobi.Bessel.edgeValue a ha k • ((1/2:ℝ) • InnerProductSpace.rankOne ℝ
    (fullTargetBasis a ha k:Space) (fullTargetBasis a ha k:Space))=_
  rw [smul_smul]
  congr 1
  rw [jacobi.Bessel.edgeValue]
  ring

/-- The actual embedded finite spectral inverses converge in genuine
trace norm to the same original continuum Green inverse.
Use: finiteNuclearGreen_operator turns this into the direct printed
matrix/isometry/adjoint convergence assertion of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: the actual embedded fixed eigenvectors converge in L2. Genuine
nuclear rank-one formation is continuous, and their half-projectors
have one proved complete spectral bound. Sum them against the actual
L1-convergent finite Jacobi spectra in the nuclear-norm Banach space. -/
theorem finiteNuclearGreen_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    Tendsto (fun n:ℕ => finiteNuclearGreen a b ha hb n) atTop (𝓝 (targetNuclearGreen a ha)) := by
  -- The summation takes place in the nuclear topology, not merely in operator norm.
  apply weighted_series_normed
    (fun n => jacobi.Jacobi.finiteLambdaAt_summable ha hb (n+1))
    (jacobi.Bessel.edgeValue_summable ha)
    ((jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).comp (tendsto_add_atTop_nat 1))
    (C:=1) (Eventually.of_forall (fun n k => embedded_half_projector_bound a b ha hb n k))
  intro k
  have hv := embeddedTargetEigenvector_limit ha hb k
  exact ((traceRankOne_bilinear (E:=Space)).continuous.continuousAt.tendsto.comp (hv.prodMk_nhds hv)).const_smul (1/2:ℝ)

end
end jacobi.Comparison

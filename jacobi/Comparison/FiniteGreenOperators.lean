import jacobi.Comparison.GreenSpectral
import jacobi.Comparison.EmbeddedEigenvectors
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Article: jacobi, Theorem 2.1.
The actual scaled finite Green matrix has exactly the rank-one spectral
expansion used by the nuclear convergence argument. Transport by the
original physical step map and its genuine adjoint preserves that same
expansion, connecting the direct matrix inverse with its finite spectrum.
Use: embeddedGreenOperator transports this actual inverse by U_N and its adjoint, as in the printed operator convergence of Theorem 2.1.
-/
namespace jacobi.Comparison
noncomputable section
open Real Matrix jacobi.Reference jacobi.Analysis
open scoped InnerProductSpace

/-- The original finite inverse in the article's exact 2*N^2 scaling,
represented as its genuine finite Euclidean continuous linear operator.
Use: embeddedGreenOperator transports this actual inverse by U_N and
its adjoint, as in the printed operator convergence of Theorem 2.1.
Article: jacobi, Theorem 2.1.
-/
def finiteGreenOperator (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    EuclideanSpace ℝ (Fin (n+1))→L[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
  Matrix.toEuclideanCLM (𝕜:=ℝ) ((1/(2*((n:ℝ)+1)^2)) • (targetChain a b ha hb n).green)

/-- The actual finite scaled inverse has exactly its original finite
rank-one expansion in the genuine signed spectral vectors.
Use: finiteNuclearGreen_operator identifies the nuclear spectral
inverse with the same direct original finite matrix operator.
Article: jacobi, Theorem 2.1.
Proof: use the community matrix/rank-one correspondence and the
proved original full Green-entry spectral formula. Each scalar
coefficient is exactly the actual reciprocal finite spectral gap. -/
theorem finiteGreenOperator_spectral (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    finiteGreenOperator a b ha hb n=∑k:Fin (n+1),
      (jacobi.Jacobi.finiteLambda a b ha hb (n+1) k/2) • InnerProductSpace.rankOne ℝ
        (finiteTargetEigenvector a b ha hb n k.val) (finiteTargetEigenvector a b ha hb n k.val) := by
  -- Compare the unchanged original matrices via the injective Euclidean operator correspondence.
  apply ContinuousLinearMap.coe_injective
  apply Matrix.toEuclideanLin.symm.injective
  simp only [finiteGreenOperator,Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,LinearEquiv.symm_apply_apply,
    ContinuousLinearMap.toLinearMap_sum,ContinuousLinearMap.toLinearMap_smul,map_sum,map_smul,
    InnerProductSpace.symm_toEuclideanLin_rankOne]
  ext i j
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,Matrix.vecMulVec_apply,star_trivial]
  have hg := jacobi.Finite.green_entry_spectral (targetMeasure a b ha hb n).reconstructed
    (targetMeasure a b ha hb n).reconstructedBasis
    (fun k => (sub_pos.mpr ((jacobi.Jacobi.nodes a b ha hb (n+1)).interval k).2).ne') i j
  change (1/(2*((n:ℝ)+1)^2))*(targetMeasure a b ha hb n).reconstructed.green i j=_
  rw [hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [jacobi.Jacobi.finiteLambda_node ha hb k]
  simp only [finiteTargetEigenvector,targetEigenvectorEntry,dite_eq_left k.isLt]
  push_cast
  field_simp
  rfl

/-- The direct original finite inverse transported into the actual
physical interval by the genuine step isometry and its Hilbert adjoint.
Use: embeddedGreenOperator_trace_limit is the literal operator claim
of Theorem 2.1, with its original U_N rather than a spectral surrogate.
Article: jacobi, Theorem 2.1.
-/
def embeddedGreenOperator (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) : Space→L[ℝ] Space :=
  (fullStepIsometry n).toContinuousLinearMap ∘L finiteGreenOperator a b ha hb n ∘L
    (fullStepIsometry n).toContinuousLinearMap.adjoint

/-- Transporting a genuine rank-one operator by any actual Hilbert
map and its adjoint gives the projector of its actual mapped vector.
Use: embeddedGreenOperator_spectral connects the original direct
finite inverse with the exact nuclear spectral expansion in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Source: the defining Hilbert adjoint identity.
Proof: evaluate on an arbitrary Hilbert vector and apply the original
adjoint inner-product identity before the same map's scalar linearity. -/
theorem rankOne_transport {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U:E→L[ℝ] F) (v:E) :
    U ∘L InnerProductSpace.rankOne ℝ v v ∘L U.adjoint=InnerProductSpace.rankOne ℝ (U v) (U v) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,InnerProductSpace.rankOne_apply,map_smul,
    ContinuousLinearMap.adjoint_inner_right]

/-- The same actual embedded finite Green inverse has exactly the
original embedded-eigenvector rank-one expansion.
Use: finiteNuclearGreen_operator identifies it with the actual nuclear
series whose convergence has been proved in trace norm.
Article: jacobi, Theorem 2.1.
Proof: insert the proved original finite spectral expansion into the
same step-map/adjoint composition; finite linearity and genuine rank-one
transport give precisely the original actual embedded vectors. -/
theorem embeddedGreenOperator_spectral (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    embeddedGreenOperator a b ha hb n=∑k:Fin (n+1),
      (jacobi.Jacobi.finiteLambda a b ha hb (n+1) k/2) • InnerProductSpace.rankOne ℝ
        (embeddedTargetEigenvector a b ha hb n k.val) (embeddedTargetEigenvector a b ha hb n k.val) := by
  -- Evaluate the finite composition so the original adjoint and finite sum remain explicit.
  unfold embeddedGreenOperator
  rw [finiteGreenOperator_spectral]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun v:Space => (jacobi.Jacobi.finiteLambda a b ha hb (n+1) k/2) • v)
    (congrArg (fun T:Space→L[ℝ] Space => T x)
      (rankOne_transport (fullStepIsometry n).toContinuousLinearMap
        (finiteTargetEigenvector a b ha hb n k.val)))

end
end jacobi.Comparison

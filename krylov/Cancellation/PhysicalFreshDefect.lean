import krylov.Cancellation.WindowResidualMetric
import krylov.LinearAlgebra.FreshDefectGeometry
import krylov.LinearAlgebra.MatrixSymmetricFamily
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), original physical matrix fresh witnesses.
Use: realize the sharp projected fresh defect by actual symmetric physical
matrices under the article's genuine relative spectral budget.
Source: the proved Householder image witness, the true Euclidean matrix/operator
equivalence and exact positive-root congruence; no whitening premise is supplied.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- Every independent nonempty physical window has its full fresh radius
attained by a real symmetric physical matrix in the original relative budget.
Use: the projected lower bound and its attainer concern precisely the original
energy metric, not a relaxed operator uncertainty class.
Article: main_krylov, apH:dcs2(a), physical symmetric fresh witness.
Proof: the genuine invertible metric root sends an actual nonzero window
column to a nonzero canonical column. The proved reflection construction
attains the full projected radius there. Its actual inverse matrix image,+conjugated by the true root, is symmetric and has exactly the same relative
budget and actual physical gradient action. -/
theorem physical_fresh_projection_witness (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hs : LinearIndependent ℝ s) (hp : 0<p)
    (step c : EuclideanSpace ℝ (Fin n)) (omega : ℝ) (homega : 0≤omega) :
    ∃ F : Matrix (Fin n) (Fin n) ℝ,F.IsSymm ∧ ‖relativeOperator base F‖≤omega ∧
      windowMetricResidual base s (cgOperator F step)=omega*‖cgOperator (metricRoot base) step‖ ∧
      omega*‖cgOperator (metricRoot base) step‖≤
        max (windowMetricResidual base s (c+cgOperator F step))
          (windowMetricResidual base s (c-cgOperator F step)) := by
  let R := cgOperator (metricRoot base)
  let C := cgOperator (metricRoot base)⁻¹
  let K := Submodule.span ℝ (Set.range (primalWindow base s))
  have hK : K≠⊥ := by
    intro hz
    let i : Fin p := ⟨0,hp⟩
    have hm : R (s i)∈K := Submodule.subset_span (Set.mem_range_self i)
    rw [hz,Submodule.mem_bot] at hm
    have he := congrArg C hm
    change C (R (s i))=C 0 at he
    have hcancel : C (R (s i))=s i := canonical_primal_dual_cancel base hb (s i)
    rw [hcancel,map_zero] at he
    exact hs.ne_zero i he
  obtain ⟨T,hTs,hT,himage,hlower⟩ := projected_fresh_two_scenarios K hK (R step) (C c) omega homega
  let M := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.symm T
  have hMop : cgOperator M=T :=
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.apply_symm_apply T
  have hMs : M.IsSymm := by
    apply Matrix.isHermitian_iff_isSymm.mp
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    change (cgOperator M).toLinearMap.IsSymmetric
    rw [hMop]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTs
  let F := metricRoot base*M*metricRoot base
  have hFs : F.IsSymm := by
    dsimp only [F]
    simp only [Matrix.IsSymm,transpose_mul,(metricRoot_isSymm base).eq,hMs.eq,Matrix.mul_assoc]
  have hrel : relativeOperator base F=M := by
    dsimp only [relativeOperator,F]
    calc
      _=((metricRoot base)⁻¹*metricRoot base)*M*(metricRoot base*(metricRoot base)⁻¹) := by noncomm_ring
      _=M := by rw [nonsing_inv_mul _ (metricRoot_det_unit base hb),
        mul_nonsing_inv _ (metricRoot_det_unit base hb),Matrix.one_mul,Matrix.mul_one]
  have haction : C (cgOperator F step)=T (R step) := by
    change cgOperator (metricRoot base)⁻¹ (cgOperator (metricRoot base*M*metricRoot base) step)=_
    simp only [cgOperator,map_mul,mul_apply_eq_comp]
    rw [canonical_primal_dual_cancel base hb]
    exact congrArg (fun L => L (R step)) hMop
  refine ⟨F,hFs,?_,?_,?_⟩
  · rw [hrel,← Matrix.l2_opNorm_toEuclideanCLM]
    change ‖cgOperator M‖≤omega
    rw [hMop]
    exact hT
  · change ‖K.starProjection (C (cgOperator F step))‖=omega*‖R step‖
    rw [haction]
    exact himage
  · change omega*‖R step‖≤max ‖K.starProjection (C (c+cgOperator F step))‖
      ‖K.starProjection (C (c-cgOperator F step))‖
    rw [map_add,map_sub,haction]
    exact hlower

end
end krylov.Cancellation

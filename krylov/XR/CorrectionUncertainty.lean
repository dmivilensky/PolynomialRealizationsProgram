import krylov.XR.RelativeCorrection
import krylov.LinearAlgebra.MatrixSymmetricFamily

/-!
Article: main_krylov, thm:metric, original physical uncertainty maximum.
Use: identify the actual norm objective with a genuinely attained maximum
over symmetric physical model errors, then state the critical segment in
physical correction coordinates. Source: the existing exact symmetric-ball
attainer, the isometric matrix/operator dictionary and positive-root transport.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference krylov.Nonlinear krylov.LinearAlgebra krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Positive-root reconstruction is exactly inverse to canonical form
normalization, including nonsymmetric errors. Article: thm:metric. -/
theorem relativeOperator_root_congruence (T X : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef) :
    relativeOperator T (metricRoot T*X*metricRoot T)=X := by
  unfold relativeOperator
  calc
    _ = ((metricRoot T)⁻¹*metricRoot T)*X*(metricRoot T*(metricRoot T)⁻¹) := by noncomm_ring
    _ = _ := by rw [nonsing_inv_mul _ (metricRoot_det_unit T hT),
      mul_nonsing_inv _ (metricRoot_det_unit T hT),one_mul,mul_one]

/-- The original physical residual has exactly the true canonical
symmetric-perturbation representation. Article: s8:minimax. -/
theorem physical_correction_residual (Xi T : Matrix (Fin p) (Fin p) ℝ) (hXi : Xi.PosDef)
    (r w : EuclideanSpace ℝ (Fin p)) :
    (metricCoordinates Xi hXi).symm (r+cgOperator T w)=
      (metricCoordinates Xi hXi).symm r+
        cgOperator (relativeOperator Xi T) (metricCoordinates Xi hXi w) := by
  rw [map_add]
  congr 1
  change cgOperator (metricRoot Xi)⁻¹ (cgOperator T w)=
    cgOperator ((metricRoot Xi)⁻¹*T*(metricRoot Xi)⁻¹) (cgOperator (metricRoot Xi) w)
  simp only [cgOperator,←mul_apply_eq_comp,←map_mul,Matrix.mul_assoc]
  rw [nonsing_inv_mul _ (metricRoot_det_unit Xi hXi),mul_one]

/-- The complete original physical uncertainty maximum is attained,
with the exact robust least-squares objective for any positive metric.
No larger abstract operator scenario replaces the symmetric matrices.
Article: main_krylov, s8:minimax and thm:metric. -/
theorem physical_correction_isGreatest (Xi T : Matrix (Fin p) (Fin p) ℝ)
    (hXi : Xi.PosDef) (hT : T.IsSymm) (r w : EuclideanSpace ℝ (Fin p))
    (Omega : ℝ) (hOmega : 0≤Omega) :
    IsGreatest {v : ℝ | ∃ B : Matrix (Fin p) (Fin p) ℝ,
      B.IsSymm ∧ relativeBudget Xi (B-T)≤Omega ∧
        v=‖(metricCoordinates Xi hXi).symm (r+cgOperator B w)‖}
      (‖(metricCoordinates Xi hXi).symm r+
          cgOperator (relativeOperator Xi T) (metricCoordinates Xi hXi w)‖+
        Omega*‖metricCoordinates Xi hXi w‖) := by
  let rho := (metricCoordinates Xi hXi).symm r
  let b := metricCoordinates Xi hXi w
  let N := cgOperator (relativeOperator Xi T)
  obtain ⟨U,hUs,hU,hu⟩ := symmetric_residual_attained (rho+N b) b hOmega
  let X := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).symm U
  have hX : cgOperator X=U := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).apply_symm_apply U
  have hXs : X.IsSymm := by
    apply Matrix.isHermitian_iff_isSymm.mp
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    change (cgOperator X).toLinearMap.IsSymmetric
    rw [hX]
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hUs
  have hXn : ‖X‖≤Omega := by
    rw [←Matrix.l2_opNorm_toEuclideanCLM]
    change ‖cgOperator X‖≤Omega
    rw [hX]
    exact hU
  let B := T+metricRoot Xi*X*metricRoot Xi
  have hBs : B.IsSymm := by
    apply hT.add
    simp only [IsSymm,transpose_mul,(metricRoot_isSymm Xi).eq,hXs.eq,Matrix.mul_assoc]
  have hbudget : relativeBudget Xi (B-T)≤Omega := by
    change ‖relativeOperator Xi (B-T)‖≤Omega
    rw [show B-T=metricRoot Xi*X*metricRoot Xi by dsimp only [B]; abel,
      relativeOperator_root_congruence Xi X hXi]
    exact hXn
  have hres : (metricCoordinates Xi hXi).symm (r+cgOperator B w)=rho+N b+U b := by
    rw [physical_correction_residual]
    change rho+cgOperator (relativeOperator Xi (T+metricRoot Xi*X*metricRoot Xi)) b=_
    have he : relativeOperator Xi (T+metricRoot Xi*X*metricRoot Xi)=relativeOperator Xi T+X := by
      simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul]
      change relativeOperator Xi T+relativeOperator Xi (metricRoot Xi*X*metricRoot Xi)=_
      rw [relativeOperator_root_congruence Xi X hXi]
      rfl
    rw [he]
    simp only [cgOperator,map_add,_root_.add_apply]
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) X=U from hX]
    exact (add_assoc rho (N b) (U b)).symm
  constructor
  · refine ⟨B,hBs,hbudget,?_⟩
    rw [hres,hu]
  · rintro v ⟨B,hBs,hbudget,rfl⟩
    rw [physical_correction_residual]
    have he : relativeOperator Xi B=relativeOperator Xi T+relativeOperator Xi (B-T) := by
      simp only [relativeOperator,Matrix.mul_sub,Matrix.sub_mul]
      abel
    rw [he]
    change ‖rho+cgOperator (relativeOperator Xi T+relativeOperator Xi (B-T)) b‖≤_
    simp only [cgOperator,map_add,_root_.add_apply]
    simpa only [N,rho,b,cgOperator,add_assoc] using
      symmetric_residual_le (rho+N b) b (cgOperator (relativeOperator Xi (B-T))) hbudget

/-- The critical minimizers are the literal physical segment between
the actual inverse-model correction and zero. Article: thm:metric. -/
theorem relativeCorrection_critical_physical_iff (T : Matrix (Fin p) (Fin p) ℝ) (hT : T.PosDef)
    (r w : EuclideanSpace ℝ (Fin p)) :
    relativeCorrectionObjective T hT r 1 w=‖(metricCoordinates T hT).symm r‖ ↔
      w∈segment ℝ (relativeNewtonCorrection T hT r) 0 := by
  rw [relativeCorrection_critical_iff]
  let e := metricCoordinates T hT
  have hh := image_segment ℝ (e.toLinearEquiv.toAffineEquiv.toAffineMap)
    (relativeNewtonCorrection T hT r) 0
  change (metricCoordinates T hT) '' segment ℝ (relativeNewtonCorrection T hT r) 0=
    segment ℝ (metricCoordinates T hT (relativeNewtonCorrection T hT r)) (metricCoordinates T hT 0) at hh
  rw [relativeNewtonCorrection_coordinate,map_zero] at hh
  rw [←hh]
  constructor
  · rintro ⟨v,hv,he⟩
    exact e.injective he ▸ hv
  · intro hw
    exact ⟨w,hw,rfl⟩

end
end krylov.XR

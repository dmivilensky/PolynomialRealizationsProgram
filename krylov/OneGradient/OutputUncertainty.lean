import krylov.Information.CorrectionCompletion
set_option autoImplicit false
/-!
Article: main_krylov, thm:exact, unobserved output segment.
Use: evaluate the exact worst semantic output gradient over actual physical
symmetric output matrices, and retain the lower bound for every output decision.
Source: Rump03 symmetric-ball image theorem already proved here; actual positive
metric-root congruence reconstructs each physical output scenario.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra krylov.Information
variable {n : ℕ}

/-- The real output residual in canonical coordinates is exactly the identity
model residual plus its actual relative output perturbation.
Use: the unknown physical output matrix remains absent from the method's decision.
Article: main_krylov, thm:exact.
Proof: split the genuine physical operator into the reference and its difference,
then apply the proved actual root and canonical-form action identities. -/
theorem physical_output_balance (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (B : Matrix (Fin n) (Fin n) ℝ) (r u : EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot A)⁻¹ (r+cgOperator B u)=
      cgOperator (metricRoot A)⁻¹ r+cgOperator (metricRoot A) u+
        cgOperator (relativeOperator A (B-A)) (cgOperator (metricRoot A) u) := by
  rw [canonical_form_action A (B-A) hA u]
  have hbase : cgOperator (metricRoot A)⁻¹ (cgOperator A u)=
      cgOperator (metricRoot A) u := canonical_reference_action A hA u
  rw [← hbase]
  simp only [map_add,cgOperator,map_sub,_root_.sub_apply,map_sub]
  abel

/-- The unobserved physical output segment has the exact attained robust maximum.
Use: quantify over real physical output matrices and every actual chosen output
displacement, including zero radius, zero displacement and the critical radius one.
Article: main_krylov, thm:exact.
Proof: canonical normalization bounds every admissible physical matrix. For
attainment, lift the actual maximizing self-adjoint ball image back through the
true metric root using the proved physical symmetric-image completion. -/
theorem physical_output_maximum (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r u : EuclideanSpace ℝ (Fin n)) {omega : ℝ} (homega : 0≤omega) :
    IsGreatest {x : ℝ | ∃ B : Matrix (Fin n) (Fin n) ℝ,B.IsSymm ∧
      relativeBudget A (B-A)≤omega ∧ x=‖cgOperator (metricRoot A)⁻¹ (r+cgOperator B u)‖}
      (‖cgOperator (metricRoot A)⁻¹ r+cgOperator (metricRoot A) u‖+
        omega*‖cgOperator (metricRoot A) u‖) := by
  let R := cgOperator (metricRoot A)
  let J := cgOperator (metricRoot A)⁻¹
  let rho := J r
  let v := R u
  have hcancel (w : EuclideanSpace ℝ (Fin n)) : J (R w)=w := by
    have he := congrArg (fun M => cgOperator M w) (nonsing_inv_mul _ (metricRoot_det_unit A hA))
    change cgOperator (metricRoot A)⁻¹ (cgOperator (metricRoot A) w)=w
    simpa only [cgOperator,map_mul,mul_apply_eq_comp,map_one,one_apply_eq_self] using he
  constructor
  · obtain ⟨T,hTs,hT,hmax⟩ := symmetric_residual_attained (rho+v) v homega
    have hbound : ‖J (R (T v))‖≤omega*‖R u‖ := by
      rw [hcancel]
      exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
    obtain ⟨F,hF,hbudget,hFu⟩ := exists_relative_symmetric_image A hA u (R (T v)) homega hbound
    refine ⟨A+F,hA.1.isSymm.add hF,?_,?_⟩
    · simpa only [add_sub_cancel_left] using hbudget
    · have he : J (r+cgOperator (A+F) u)=rho+v+T v := by
        simp only [cgOperator,map_add,_root_.add_apply,map_add]
        change J r+(J (cgOperator A u)+J (cgOperator F u))=rho+v+T v
        have hbase : J (cgOperator A u)=v := canonical_reference_action A hA u
        rw [hbase,hFu,hcancel]
        abel
      rw [he]
      exact hmax.symm
  · rintro x ⟨B,hB,hbudget,rfl⟩
    rw [physical_output_balance A hA]
    have hnorm : ‖cgOperator (relativeOperator A (B-A))‖≤omega := by
      simpa only [relativeBudget,chebyshev1.opNorm,Matrix.cstar_norm_def,cgOperator] using hbudget
    exact symmetric_residual_le _ _ _ hnorm

/-- Every output decision leaves at least omega times the actual pre-output
residual when the physical output radius is at most one.
Use: the arbitrary-method minimax lower bound permits outputs depending on
the last observed gradient; it imposes no CG-consistency assumption.
Article: main_krylov, thm:exact.
Proof: the attained physical robust maximum and the proved identity-model
lower bound hold for each individual genuine chosen output displacement. -/
theorem physical_output_lower (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r u : EuclideanSpace ℝ (Fin n)) {omega : ℝ} (homega : 0≤omega) (hsmall : omega≤1) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,B.IsSymm ∧ relativeBudget A (B-A)≤omega ∧
      omega*‖cgOperator (metricRoot A)⁻¹ r‖≤‖cgOperator (metricRoot A)⁻¹ (r+cgOperator B u)‖ := by
  obtain ⟨B,hB,hbudget,he⟩ := (physical_output_maximum A hA r u homega).1
  refine ⟨B,hB,hbudget,?_⟩
  rw [← he]
  simpa only [min_eq_right hsmall] using robust_identity_lower
    (cgOperator (metricRoot A)⁻¹ r) (cgOperator (metricRoot A) u) homega

end
end krylov.OneGradient

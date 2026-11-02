import krylov.OneGradient.TwoQueryInformation
import krylov.Information.KnownBasePlanar
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), original physical arbitrary-output game.
Use: transfer the finite hidden-model lower bound to genuine complete
one-gradient executions and actual symmetric relative-budget output matrices.
Source: true history indistinguishability, actual positive-root conjugacy,
the attained symmetric operator ball and the real matrix/operator dictionary.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Secant krylov.Information
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual unevaluated one-gradient semantic output has exactly its
true normalized gradient and normalized physical operator action.
Use: original physical executions retain their genuine reference metric
in finite hidden-model minimax lower bounds.
Article: main_krylov, thm:local(c), true physical residual coordinates.
Proof: the real inverse metric root preserves addition, and the actual
positive-root action dictionary identifies the real output operator form. -/
theorem twoQuery_canonical_output
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n))) (H : History (EuclideanSpace ℝ (Fin n))) :
    cgOperator (metricRoot A)⁻¹ (m.outputGradient (cgOperator B) H)=
      cgOperator (metricRoot A)⁻¹ H.gradient+
        cgOperator (relativeOperator A B) (cgOperator (metricRoot A) (m.output H)) := by
  rw [OneGradientMethod.outputGradient,map_add,← canonical_form_action A B hA]

/-- Every arbitrary actual two-query method admits a genuine symmetric
relative-budget output matrix attaining the finite hidden-model lower
bound on its real common-data fibre, with the original physical metric.
No CG consistency, smoothness, bounded output or limiting-policy premise
is imposed. The entire true histories, rather than only final gradients,
are equal on the hidden pair.
Use: the original M1 minimax lower bound has real physical adversaries
and a finite inverse-free loss before taking any perturbation limit.
Article: main_krylov, thm:local(c), genuine physical arbitrary-output game.
Proof: the exact observed-action identity gives the common real output.
Apply the finite game in the genuine positive-root coordinates. Its
attaining self-adjoint output operator has a true symmetric matrix, whose
actual inverse-root physical transport preserves precisely the original
relative spectral budget. Exact canonical output identities identify
both genuine semantic residuals with the real game residuals. -/
theorem twoQuery_physical_hidden_lower
    (A C D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n))
    (hD : cgOperator D (m.step (oneGradientRun m (fun _ => cgOperator A) g 1))=0)
    (w : ℝ) (hw : 0< w) :
    let H := oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator C)) g 2
    let rho := cgOperator (metricRoot A)⁻¹ H.gradient
    let Delta := cgOperator (relativeOperator A D)
    let Center := cgOperator (relativeOperator A C)
    ∃ F : Matrix (Fin n) (Fin n) ℝ,F.IsSymm ∧ relativeBudget A F≤ w ∧
      ‖Delta rho‖+w*‖rho‖≤
        (1+(‖Delta‖+w)+(‖Delta‖+w)*‖Center-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖/w)*
          max ‖cgOperator (metricRoot A)⁻¹ (m.outputGradient (cgOperator (C+D+F))
            (oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C+D))) g 2))‖
            ‖cgOperator (metricRoot A)⁻¹ (m.outputGradient (cgOperator (C-D+F))
              (oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C-D))) g 2))‖ := by
  let H := oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator C)) g 2
  let rho := cgOperator (metricRoot A)⁻¹ H.gradient
  let u := cgOperator (metricRoot A) (m.output H)
  let Delta := cgOperator (relativeOperator A D)
  let Center := cgOperator (relativeOperator A C)
  let K := 1+(‖Delta‖+w)+(‖Delta‖+w)*‖Center-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖/w
  have hK : 0≤ K := by dsimp only [K];positivity
  have hlower := twoModelRisk_centred_lower Center Delta rho u w hw
  have hattain := twoModelRisk_attained Center Delta rho u w hw.le
  rcases hattain with ⟨Fop,hFs,hFn,hFe⟩|⟨Fop,hFs,hFn,hFe⟩ <;>
    let FM := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm Fop <;>
    let F := inverseFormMap (metricRoot A)⁻¹ FM
  all_goals
    have hFM : FM.IsSymm := by
      apply Matrix.isHermitian_iff_isSymm.mp
      apply Matrix.isSymmetric_toEuclideanLin_iff.mp
      have he : cgOperator FM=Fop := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _
      change (cgOperator FM).toLinearMap.IsSymmetric
      rw [he]
      exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hFs
    have hrel : relativeOperator A F=FM := relativeOperator_inverseRootForm A FM hA
    have hFop : cgOperator (relativeOperator A F)=Fop := by
      rw [hrel]
      exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).apply_symm_apply _
    refine ⟨F,inverseForm_isSymm _ _ hFM,?_,?_⟩
    · change ‖cgOperator (relativeOperator A F)‖≤ w
      rw [hFop]
      exact hFn
    · have hh := twoQuery_hidden_histories m (cgOperator A) (cgOperator C) (cgOperator D) g hD
      have hp : oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C+D))) g 2=H := by
        simpa only [H,cgOperator,map_add] using hh.1
      have hm : oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C-D))) g 2=H := by
        simpa only [H,cgOperator,map_sub] using hh.2
      rw [hp,hm,twoQuery_canonical_output A (C+D+F) hA,twoQuery_canonical_output A (C-D+F) hA]
      have heP : cgOperator (relativeOperator A (C+D+F))=Center+Delta+Fop := by
        simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul,cgOperator,map_add] at hFop ⊢
        rw [hFop]
        rfl
      have heM : cgOperator (relativeOperator A (C-D+F))=Center-Delta+Fop := by
        simp only [relativeOperator,Matrix.mul_add,Matrix.add_mul,Matrix.mul_sub,Matrix.sub_mul,cgOperator,map_add,map_sub] at hFop ⊢
        rw [hFop]
        rfl
      rw [heP,heM]
      change _≤ K*max ‖rho+(Center+Delta+Fop) u‖ ‖rho+(Center-Delta+Fop) u‖
      apply hlower.trans
      apply mul_le_mul_of_nonneg_left _ hK
      simp only [_root_.add_apply,_root_.sub_apply,add_assoc] at hFe ⊢
      first
      | rw [← hFe];exact le_max_left _ _
      | rw [← hFe];exact le_max_right _ _

end
end krylov.OneGradient

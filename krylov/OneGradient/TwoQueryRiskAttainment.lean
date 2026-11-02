import krylov.OneGradient.TwoQueryPhysicalGame
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), actual robust risk attainment.
Use: a real physical output matrix witnesses the complete finite hidden
model game at every arbitrary actual common-data output.
Source: genuine symmetric-ball attainment, actual complete-history
indistinguishability and exact positive-root physical transport.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Secant krylov.Information
open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual two-query hidden-model robust game is bounded above by
the genuine physical residual on one of its two completions with one
real symmetric output matrix of the original relative budget. The true
histories include every observed record, and the output is arbitrary.
Use: all finite game inequalities apply to the original physical scenario
supremum without assuming any output regularity or boundedness.
Article: main_krylov, thm:local(c), genuine physical game realization.
Proof: attain the larger hidden-completion residual by the actual symmetric
operator ball. Transport that true operator to a physical symmetric form;
its relative budget is exact. Actual complete-history equality and the
positive-root dictionary identify both genuine semantic residuals. -/
theorem twoQuery_physical_risk_attained
    (A C D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (m : OneGradientMethod (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n))
    (hD : cgOperator D (m.step (oneGradientRun m (fun _ => cgOperator A) g 1))=0)
    (w : ℝ) (hw : 0< w) :
    let H := oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator C)) g 2
    let rho := cgOperator (metricRoot A)⁻¹ H.gradient
    let Delta := cgOperator (relativeOperator A D)
    let Center := cgOperator (relativeOperator A C)
    ∃ F : Matrix (Fin n) (Fin n) ℝ,F.IsSymm ∧ relativeBudget A F≤ w ∧
      twoModelRisk Center Delta rho (cgOperator (metricRoot A) (m.output H)) w≤
          max ‖cgOperator (metricRoot A)⁻¹ (m.outputGradient (cgOperator (C+D+F))
            (oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C+D))) g 2))‖
            ‖cgOperator (metricRoot A)⁻¹ (m.outputGradient (cgOperator (C-D+F))
              (oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator (C-D))) g 2))‖ := by
  let H := oneGradientRun m (twoQueryOperators (cgOperator A) (cgOperator C)) g 2
  let rho := cgOperator (metricRoot A)⁻¹ H.gradient
  let u := cgOperator (metricRoot A) (m.output H)
  let Delta := cgOperator (relativeOperator A D)
  let Center := cgOperator (relativeOperator A C)
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
      change twoModelRisk Center Delta rho u w≤max ‖rho+(Center+Delta+Fop) u‖ ‖rho+(Center-Delta+Fop) u‖
      simp only [_root_.add_apply,_root_.sub_apply,add_assoc] at hFe ⊢
      first
      | rw [← hFe];exact le_max_left _ _
      | rw [← hFe];exact le_max_right _ _

end
end krylov.OneGradient

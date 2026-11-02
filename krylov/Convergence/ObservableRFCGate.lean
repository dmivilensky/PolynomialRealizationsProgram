import krylov.Convergence.ObservableRFCModel
import krylov.Convergence.ObservableRFCAlgebra

/-!
Article: main_krylov, apG:Dunif, the genuine observed RFC energy gate.
Use: interpret both outcomes of the literal computed square-root test
using the actual searched segment, before any correction is accepted.
Source: true metric secant identities, positive averaged curvature and
the proved model-energy/synthesis comparison. No step floor is used.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual measured denominator is precisely the true canonical
quadratic curvature of the real searched step. Article: apG:Dunif. -/
theorem ObservableRFCPrepared.denominator {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {epsilon : ℝ}
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) :
    inner ℝ (rfcFunctionLineStep T f fullMemory r x₀ B)
      (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)=
      inner ℝ (T (rfcFunctionLineStep T f fullMemory r x₀ B))
        (observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionLineStep T f fullMemory r x₀ B))) := by
  have hy : T.symm (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)=
      observableRFCSearchOperator T f H r x₀ B (T (rfcFunctionLineStep T f fullMemory r x₀ B)) := by
    rw [map_sub]
    change observableRFCLineGradient T f G r x₀ B-T.symm B.gradient=_
    rw [P.searched,P.line,map_smul,searchedGradient,add_sub_cancel_left]
  rw [←inverse_symmetric_pairing T hT,hy]

/-- The true line denominator is positive with absolute 7/8 and 9/8
bounds, even when the actual searched step is arbitrarily short.
Article: main_krylov, apG:Dunif. -/
theorem ObservableRFCPrepared.curvature {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {epsilon : ℝ}
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (he : epsilon≤1/8) :
    let D := inner ℝ (rfcFunctionLineStep T f fullMemory r x₀ B)
      (G (rfcFunctionLinePoint T f fullMemory r x₀ B)-B.gradient)
    0 < D ∧ (7/8:ℝ)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖^2≤D ∧
      D≤(9/8:ℝ)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖^2 := by
  dsimp only
  rw [P.denominator hT]
  have hh := observable_operator_form _ epsilon P.operator (T (rfcFunctionLineStep T f fullMemory r x₀ B))
  have hn := norm_pos_iff.mpr P.step
  refine ⟨?_,?_,?_⟩
  · nlinarith only [hh.1,he,sq_pos_of_pos hn]
  · nlinarith only [hh.1,mul_le_mul_of_nonneg_right he (sq_nonneg ‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖)]
  · nlinarith only [hh.2,mul_le_mul_of_nonneg_right he (sq_nonneg ‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖)]

/-- An actual passed observable test bounds the genuine proposed
correction, without an assumed accepted-step inequality.
Article: main_krylov, apG:Dunif. -/
theorem ObservableRFCPrepared.passed {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {epsilon bar : ℝ}
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (he : epsilon≤1/8) (hb : 0≤bar)
    (hg : observableCorrectionRatio T f G r x₀ B≤bar) :
    ‖T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)‖≤
      (3/2:ℝ)*bar*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖ := by
  have hc := P.curvature hT he
  rw [observableCorrectionRatio,P.energy] at hg
  rw [P.correction]
  exact observable_energy_gate_pass _ _ _ _ bar P.energy_nonneg hc.1 (norm_nonneg _) hb P.move_energy hc.2.2 hg

/-- An actual failed observable test forces the genuine proposed
correction to be large relative to the actual line. Article: apG:Dunif. -/
theorem ObservableRFCPrepared.failed {T : E ≃L[ℝ] E} {f : E → ℝ} {G : E → E}
    {H : E → E →L[ℝ] E} {r : ℝ} {x₀ : E} {B : History E} {epsilon bar : ℝ}
    (P : ObservableRFCPrepared T f G H r x₀ B epsilon)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (he : epsilon≤1/8) (hb : 0≤bar)
    (hg : bar<observableCorrectionRatio T f G r x₀ B) :
    (bar/2)*‖T (rfcFunctionLineStep T f fullMemory r x₀ B)‖<
      ‖T (rfcFunctionCorrectionStep T f G fullMemory r x₀ B)‖ := by
  have hc := P.curvature hT he
  rw [observableCorrectionRatio,P.energy] at hg
  rw [P.correction]
  exact observable_energy_gate_fail _ _ _ _ bar P.energy_nonneg hc.1 (norm_nonneg _) hb P.energy_move hc.2.1 hg

end
end krylov.Convergence

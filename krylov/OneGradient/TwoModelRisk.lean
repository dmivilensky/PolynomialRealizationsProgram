import krylov.LinearAlgebra.SymmetricBall
import krylov.LinearAlgebra.InformationRadius
import Mathlib.Analysis.Normed.Operator.NormedSpace
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite hidden-model/output-defect game.
Use: derive a finite perturbation lower bound at arbitrary actual common
outputs, without assuming that a competing method has a regular limit.
Source: actual symmetric-ball attainments, the true two-scenario norm
bound and exact norm-seminorm triangle estimates.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.LinearAlgebra
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine worst residual over two actual hidden model completions
and the independent symmetric output-defect ball at one common output.
Use: finite known-base information lower bounds retain arbitrary outputs.
Article: main_krylov, thm:local(c), hidden-entry two-model game. -/
def twoModelRisk (C D : E →L[ℝ] E) (rho u : E) (w : ℝ) : ℝ :=
  max (‖rho+(C+D) u‖+w*‖u‖) (‖rho+(C-D) u‖+w*‖u‖)

/-- Both the common centre residual and genuine hidden-model action
are bounded by the actual two-model robust risk after removing the
same independent output-defect norm term.
Use: no bounded output, CG consistency or asymptotic policy limit is
assumed in the finite hidden-model obstruction.
Article: main_krylov, thm:local(c).
Proof: the sum and difference of the actual two model residuals give
twice the genuine centre and hidden action; the triangle inequality
bounds both by their actual maximum. -/
theorem twoModelRisk_bounds (C D : E →L[ℝ] E) (rho u : E) (w : ℝ) :
    ‖rho+C u‖+w*‖u‖≤ twoModelRisk C D rho u w ∧
      ‖D u‖+w*‖u‖≤ twoModelRisk C D rho u w := by
  let a := rho+C u
  let b := D u
  let M := max ‖a+b‖ ‖a-b‖
  have hp : ‖a+b‖≤ M := le_max_left _ _
  have hm : ‖a-b‖≤ M := le_max_right _ _
  have hplus : (a+b)+(a-b)=(2 : ℝ) • a := by simp only [two_smul];abel
  have hminus : (a+b)-(a-b)=(2 : ℝ) • b := by simp only [two_smul];abel
  have hc := norm_add_le (a+b) (a-b)
  have hd := norm_sub_le (a+b) (a-b)
  rw [hplus,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hc
  rw [hminus,norm_smul,Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)] at hd
  have hpos : rho+(C+D) u=a+b := by
    change rho+(C u+D u)=(rho+C u)+D u
    abel
  have hneg : rho+(C-D) u=a-b := by
    change rho+(C u-D u)=(rho+C u)-D u
    abel
  have hRisk : twoModelRisk C D rho u w=M+w*‖u‖ := by
    rw [twoModelRisk,hpos,hneg,← max_add_add_right]
  rw [hRisk]
  change ‖a‖+w*‖u‖≤ M+w*‖u‖ ∧ ‖b‖+w*‖u‖≤ M+w*‖u‖
  constructor <;> linarith

/-- The finite hidden-model game controls the genuine centred residual
seminorm at every arbitrary common output, with an explicit finite loss.
Use: the original minimax lower bound needs no assumed O(omega²) output,
regular policy, nondegenerate last-step limit or finite-risk premise.
Article: main_krylov, thm:local(c), finite arbitrary-output lower bound.
Proof: the actual two-model bounds control both the centre residual and
the hidden/output seminorm of the common correction. Split rho into its
true centre residual, minus the actual model change applied to u, minus u.
The real operator norms give the explicit finite inverse-free loss. -/
theorem twoModelRisk_centred_lower (C D : E →L[ℝ] E) (rho u : E) (w : ℝ) (hw : 0< w) :
    ‖D rho‖+w*‖rho‖≤(1+(‖D‖+w)+(‖D‖+w)*‖C-ContinuousLinearMap.id ℝ E‖/w)*
      twoModelRisk C D rho u w := by
  let L := ‖D‖+w
  let R := twoModelRisk C D rho u w
  let v := rho+C u
  let z := (C-ContinuousLinearMap.id ℝ E) u
  have hb := twoModelRisk_bounds C D rho u w
  have hRn : 0≤ R := le_trans (by positivity : 0≤‖D u‖+w*‖u‖) hb.2
  have hu : ‖u‖≤ R/w := (le_div_iff₀ hw).mpr (by nlinarith [norm_nonneg (D u)])
  have hv : ‖v‖≤ R := by nlinarith [norm_nonneg u]
  have hz : ‖z‖≤‖C-ContinuousLinearMap.id ℝ E‖*‖u‖ :=
    (C-ContinuousLinearMap.id ℝ E).le_opNorm u
  have hsplit : rho=v-z-u := by
    change rho=(rho+C u)-(C u-u)-u
    abel
  have hDr : ‖D rho‖≤‖D v‖+‖D z‖+‖D u‖ := by
    rw [hsplit,map_sub,map_sub]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hr : ‖rho‖≤‖v‖+‖z‖+‖u‖ := by
    rw [hsplit]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hbase : ‖D rho‖+w*‖rho‖≤ L*‖v‖+L*‖z‖+R := by
    have hDv := D.le_opNorm v
    have hDz := D.le_opNorm z
    have hrw := mul_le_mul_of_nonneg_left hr hw.le
    dsimp only [L]
    nlinarith [hb.2]
  have hL : 0≤ L := by dsimp only [L];positivity
  have hlast : L*‖z‖≤ L*‖C-ContinuousLinearMap.id ℝ E‖*(R/w) := by
    calc
      _ ≤ L*(‖C-ContinuousLinearMap.id ℝ E‖*‖u‖) := mul_le_mul_of_nonneg_left hz hL
      _ = (L*‖C-ContinuousLinearMap.id ℝ E‖)*‖u‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (mul_nonneg hL (norm_nonneg _))
  have hv' := mul_le_mul_of_nonneg_left hv hL
  have heq : L*‖C-ContinuousLinearMap.id ℝ E‖*(R/w)=(L*‖C-ContinuousLinearMap.id ℝ E‖/w)*R := by ring
  rw [heq] at hlast
  change _≤(1+L+L*‖C-ContinuousLinearMap.id ℝ E‖/w)*R
  nlinarith

variable [CompleteSpace E]

/-- The actual two-model robust risk is attained by a genuine symmetric
output-defect operator on one of the two genuine hidden completions.
Use: every finite lower bound refers to real admissible operator actions,
with no relaxation to an abstract norm-ball output certificate.
Article: main_krylov, thm:local(c), actual robust game attainment.
Proof: select the larger genuine centre residual. The already proved
symmetric-ball residual construction attains its exact added norm radius. -/
theorem twoModelRisk_attained (C D : E →L[ℝ] E) (rho u : E) (w : ℝ) (hw : 0≤ w) :
    (∃ F : E →L[ℝ] E,IsSelfAdjoint F ∧ ‖F‖≤ w ∧
      ‖rho+(C+D) u+F u‖=twoModelRisk C D rho u w) ∨
    (∃ F : E →L[ℝ] E,IsSelfAdjoint F ∧ ‖F‖≤ w ∧
      ‖rho+(C-D) u+F u‖=twoModelRisk C D rho u w) := by
  by_cases hp : ‖rho+(C-D) u‖≤‖rho+(C+D) u‖
  · obtain ⟨F,hFs,hFn,hFe⟩ := symmetric_residual_attained (rho+(C+D) u) u hw
    refine Or.inl ⟨F,hFs,hFn,?_⟩
    rw [hFe,twoModelRisk,max_eq_left (by linarith)]
  · obtain ⟨F,hFs,hFn,hFe⟩ := symmetric_residual_attained (rho+(C-D) u) u hw
    refine Or.inr ⟨F,hFs,hFn,?_⟩
    rw [hFe,twoModelRisk,max_eq_right (by linarith)]

end
end krylov.OneGradient

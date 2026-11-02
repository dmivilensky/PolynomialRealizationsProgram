import krylov.Reference.CanonicalSteps
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
Article: main_krylov, thm:metric, coincidence of robust thresholds.
Use: the two actual inverse-model thresholds obey the printed moment
chain; equality saturates a genuine Cauchy--Schwarz inequality.
Source: the positive self-adjoint moment argument in the article's proof.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The actual Newton threshold of robust least squares.
Article: main_krylov, thm:metric, Omega_1. -/
def newtonThreshold (N : Matrix (Fin p) (Fin p) ℝ) (r : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ‖cgOperator N⁻¹ r‖/‖cgOperator N⁻¹ (cgOperator N⁻¹ r)‖

/-- The actual zero-correction threshold of robust least squares.
Article: main_krylov, thm:metric, Omega_2. -/
def zeroThreshold (N : Matrix (Fin p) (Fin p) ℝ) (r : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ‖cgOperator N r‖/‖r‖

/-- Cancellation of the true positive-model inverse is exact.
Article: main_krylov, thm:metric. -/
theorem threshold_inverse_cancel (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) : cgOperator N⁻¹ (cgOperator N v)=v := by
  simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'),map_one,one_apply_eq_self]

/-- A positive actual model has injective physical action.
Article: main_krylov, thm:metric. -/
theorem threshold_action_ne_zero (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (v : EuclideanSpace ℝ (Fin p)) (hv : v≠0) : cgOperator N v≠0 := by
  intro hz
  have hh := threshold_inverse_cancel N hN v
  rw [hz,map_zero] at hh
  exact hv hh.symm

/-- On the genuine variable r=N^2u both thresholds have their original
positive-moment ratios. Article: main_krylov, thm:metric. -/
theorem thresholds_at_square (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (u : EuclideanSpace ℝ (Fin p)) :
    newtonThreshold N (cgOperator N (cgOperator N u))=‖cgOperator N u‖/‖u‖ ∧
    zeroThreshold N (cgOperator N (cgOperator N u))=
      ‖cgOperator N (cgOperator N (cgOperator N u))‖/‖cgOperator N (cgOperator N u)‖ := by
  simp only [newtonThreshold,zeroThreshold,threshold_inverse_cancel N hN,and_self]

/-- Two consecutive genuine positive moment inequalities imply ordered
thresholds and a sharp equality criterion. Article: main_krylov, thm:metric. -/
theorem threshold_ratio_geometry {a b c d : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (h₁ : b^2≤a*c) (h₂ : c^2≤b*d) :
    b/a≤d/c ∧ (b/a=d/c → b^2=a*c) := by
  constructor
  · apply (div_le_div_iff₀ ha hc).mpr
    have hh₁ := mul_le_mul_of_nonneg_right h₁ hd.le
    have hh₂ := mul_le_mul_of_nonneg_left h₂ hb.le
    nlinarith
  · intro he
    have he' := (div_eq_div_iff ha.ne' hc.ne').mp he
    have hh := mul_le_mul_of_nonneg_left h₂ ha.le
    apply le_antisymm h₁
    nlinarith

/-- The real positive-model moment chain is a true inner-product
calculation, with no spectral-support premise. Article: thm:metric. -/
theorem threshold_moment_bounds (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (u : EuclideanSpace ℝ (Fin p)) :
    ‖cgOperator N u‖^2≤‖u‖*‖cgOperator N (cgOperator N u)‖ ∧
    ‖cgOperator N (cgOperator N u)‖^2≤
      ‖cgOperator N u‖*‖cgOperator N (cgOperator N (cgOperator N u))‖ := by
  have hs := (cgOperator_positive N hN).1
  have he (v : EuclideanSpace ℝ (Fin p)) :
      inner ℝ v (cgOperator N (cgOperator N v))=‖cgOperator N v‖^2 := by
    have hh := hs v (cgOperator N v)
    change inner ℝ (cgOperator N v) (cgOperator N v)=
      inner ℝ v (cgOperator N (cgOperator N v)) at hh
    rw [←hh,real_inner_self_eq_norm_sq]
  constructor
  · rw [←he]
    exact real_inner_le_norm _ _
  · rw [←he]
    exact real_inner_le_norm _ _

/-- The source's threshold inequality follows for every actual nonzero
residual. Article: main_krylov, thm:metric. -/
theorem newtonThreshold_le_zeroThreshold (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (r : EuclideanSpace ℝ (Fin p)) (hr : r≠0) : newtonThreshold N r≤zeroThreshold N r := by
  let u := cgOperator N⁻¹ (cgOperator N⁻¹ r)
  have hi (v : EuclideanSpace ℝ (Fin p)) : cgOperator N (cgOperator N⁻¹ v)=v := by
    simp only [cgOperator,←mul_apply_eq_comp,←map_mul,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN.det_pos.ne'),map_one,one_apply_eq_self]
  have he : cgOperator N (cgOperator N u)=r := by dsimp only [u]; rw [hi,hi]
  have hu : u≠0 := by intro hz; apply hr; rw [←he,hz,map_zero,map_zero]
  have hv := threshold_action_ne_zero N hN u hu
  have hw := threshold_action_ne_zero N hN _ hv
  have ht := threshold_action_ne_zero N hN _ hw
  have hm := threshold_moment_bounds N hN u
  have hh := (threshold_ratio_geometry (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
    (norm_pos_iff.mpr hw) (norm_pos_iff.mpr ht) hm.1 hm.2).1
  rw [←he,(thresholds_at_square N hN u).1,(thresholds_at_square N hN u).2]
  exact hh

/-- Coinciding actual thresholds force a true model-square eigenvector.
Article: main_krylov, thm:metric, equality on the spectral support. -/
theorem threshold_equality_square_eigenvector (N : Matrix (Fin p) (Fin p) ℝ) (hN : N.PosDef)
    (u : EuclideanSpace ℝ (Fin p)) (hu : u≠0)
    (he : newtonThreshold N (cgOperator N (cgOperator N u))=
      zeroThreshold N (cgOperator N (cgOperator N u))) :
    ‖cgOperator N (cgOperator N u)‖ • u=‖u‖ • cgOperator N (cgOperator N u) := by
  have hv := threshold_action_ne_zero N hN u hu
  have hw := threshold_action_ne_zero N hN _ hv
  have ht := threshold_action_ne_zero N hN _ hw
  rw [(thresholds_at_square N hN u).1,(thresholds_at_square N hN u).2] at he
  have hm := threshold_moment_bounds N hN u
  have hh := (threshold_ratio_geometry (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
    (norm_pos_iff.mpr hw) (norm_pos_iff.mpr ht) hm.1 hm.2).2 he
  apply inner_eq_norm_mul_iff_real.mp
  have hs := (cgOperator_positive N hN).1
  have hi := hs u (cgOperator N u)
  change inner ℝ (cgOperator N u) (cgOperator N u)=
    inner ℝ u (cgOperator N (cgOperator N u)) at hi
  rw [←hi,real_inner_self_eq_norm_sq]
  exact hh

end
end krylov.XR

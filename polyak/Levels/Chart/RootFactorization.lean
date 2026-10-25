import polyak.Levels.Chart.ContinuousRoots

/-! The four continuous source-quartic root labels, with their
multiplicities witnessed by the complete factorization. -/
noncomputable section
namespace polyak.Levels.Chart
open General

theorem reverse_root_factor (C : CoefficientPoint) (z : ℂ) :
    ((inverseTuning C).beta:ℂ)*(z-(bRootPlus C)⁻¹)*(z-(bRootMinus C)⁻¹)=
      (inverseTuning C).beta*z^2-(1+(inverseTuning C).beta-(inverseTuning C).y:ℝ)*z+1 := by
  have hs : bRootPlus C+bRootMinus C=(1+(inverseTuning C).beta-(inverseTuning C).y:ℝ) := by
    unfold bRootPlus bRootMinus rootPlus rootMinus
    ring
  have hp : bRootPlus C*bRootMinus C=((inverseTuning C).beta:ℂ) := by
    simpa only [bRootPlus,bRootMinus,zero_sub,neg_mul_neg,zero_pow (by norm_num : 2≠0),mul_zero,sub_zero,zero_add] using
      root_factor (1+(inverseTuning C).beta-(inverseTuning C).y) (inverseTuning C).beta 0
  rw [←hp,←hs]
  field_simp [bRootPlus_ne_zero C,bRootMinus_ne_zero C]
  ring

theorem quartic_continuous_roots_factor (C : CoefficientPoint) {z : ℂ} (hz : z≠0) :
    (2*(inverseTuning C).B*(1-(inverseTuning C).beta):ℝ)*(quartic C.val).eval z=
      -((inverseTuning C).beta:ℂ)*(z-aRootPlus C)*(z-aRootMinus C)*
        (z-(bRootPlus C)⁻¹)*(z-(bRootMinus C)⁻¹) := by
  have ha : (inverseTuning C).a z=(z-aRootPlus C)*(z-aRootMinus C) :=
    (root_factor (1+(inverseTuning C).beta-(inverseTuning C).x) (inverseTuning C).beta z).symm
  rw [constructed_quartic_factor C hz,ha,←reverse_root_factor C z]
  ring

end polyak.Levels.Chart

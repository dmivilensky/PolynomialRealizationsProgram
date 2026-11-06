import nesterov.Oracle.ExtensionData
import polyak.Basic

/-! The simplex maximum has its actual everywhere gradient and the
claimed sharp smoothness/strong-convexity constants. -/
namespace nesterov.Oracle.ExtensionData
noncomputable section
open Set
open scoped Topology
variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Oracle.ExtensionData I E)

theorem support_cocoercive (x y : E) :
    ‖D.support x-D.support y‖^2≤
      (1-D.q)*inner ℝ (D.support x-D.support y) (x-y) := by
  have hx := D.optimizer_strong x (D.optimizer_weights y)
  have hy := D.optimizer_strong y (D.optimizer_weights x)
  change D.raw x (D.optimizer y)+‖D.support y-D.support x‖^2/(2*(1-D.q))≤
    D.raw x (D.optimizer x) at hx
  change D.raw y (D.optimizer x)+‖D.support x-D.support y‖^2/(2*(1-D.q))≤
    D.raw y (D.optimizer y) at hy
  rw [norm_sub_rev (D.support y)] at hx
  have h : ‖D.support x-D.support y‖^2/(1-D.q)≤
      inner ℝ (D.support x-D.support y) (x-y) := by
    dsimp only [raw] at hx hy
    change inner ℝ (D.support y) x-‖D.support y‖^2/(2*(1-D.q))+_+_≤
      inner ℝ (D.support x) x-‖D.support x‖^2/(2*(1-D.q))+_ at hx
    change inner ℝ (D.support x) y-‖D.support x‖^2/(2*(1-D.q))+_+_≤
      inner ℝ (D.support y) y-‖D.support y‖^2/(2*(1-D.q))+_ at hy
    simp only [inner_sub_left,inner_sub_right]
    have hd : ‖D.support x-D.support y‖^2/(1-D.q)=2*(‖D.support x-D.support y‖^2/(2*(1-D.q))) := by
      field_simp [(sub_pos.mpr D.q_lt_one).ne']
    rw [hd]
    linarith
  have hh := (div_le_iff₀ (sub_pos.mpr D.q_lt_one)).mp h
  nlinarith

theorem support_lipschitz (x y : E) : ‖D.support x-D.support y‖≤(1-D.q)*‖x-y‖ := by
  have h := (D.support_cocoercive x y).trans
    (mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (sub_pos.mpr D.q_lt_one).le)
  by_cases hz : ‖D.support x-D.support y‖=0
  · rw [hz]
    exact mul_nonneg (sub_pos.mpr D.q_lt_one).le (norm_nonneg _)
  have hp : 0<‖D.support x-D.support y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  nlinarith

theorem field_lipschitz (x y : E) : ‖D.field x-D.field y‖≤‖x-y‖ := by
  have he : D.field x-D.field y=D.q • (x-y)+(D.support x-D.support y) := by
    dsimp only [field]
    module
  rw [he]
  calc
    _≤‖D.q • (x-y)‖+‖D.support x-D.support y‖ := norm_add_le _ _
    _≤D.q*‖x-y‖+(1-D.q)*‖x-y‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos D.q_pos]
      exact add_le_add le_rfl (D.support_lipschitz x y)
    _=‖x-y‖ := by ring

theorem potential_lower (x y : E) :
    D.potential x+inner ℝ (D.field x) (y-x)+D.q/2*‖y-x‖^2≤D.potential y := by
  have h := D.optimizer_max y (D.optimizer x) (D.optimizer_weights x)
  dsimp only [potential,field,raw,support] at h ⊢
  simp only [inner_add_left,real_inner_smul_left,inner_sub_right,norm_sub_sq_real,
    real_inner_self_eq_norm_sq] at h ⊢
  rw [real_inner_comm y x]
  nlinarith

theorem potential_upper (x y : E) :
    D.potential y≤D.potential x+inner ℝ (D.field x) (y-x)+(1/2:ℝ)*‖y-x‖^2 := by
  have h := D.optimizer_strong x (D.optimizer_weights y)
  change D.raw x (D.optimizer y)+‖D.support y-D.support x‖^2/(2*(1-D.q))≤
    D.raw x (D.optimizer x) at h
  have ha : 0<1-D.q := sub_pos.mpr D.q_lt_one
  have hs : inner ℝ (D.support y-D.support x) (y-x)-
      ‖D.support y-D.support x‖^2/(2*(1-D.q))≤(1-D.q)/2*‖y-x‖^2 := by
    have hc := real_inner_le_norm (D.support y-D.support x) (y-x)
    have hh := sq_nonneg (‖D.support y-D.support x‖-(1-D.q)*‖y-x‖)
    have hm := mul_le_mul_of_nonneg_left hc (show 0≤2*(1-D.q) by linarith)
    calc
      _=(2*(1-D.q)*inner ℝ (D.support y-D.support x) (y-x)-
          ‖D.support y-D.support x‖^2)/(2*(1-D.q)) := by
        field_simp [ha.ne']
      _≤_ := (div_le_iff₀ (by positivity : (0:ℝ)<2*(1-D.q))).mpr (by nlinarith)
  dsimp only [potential,field,raw,support] at h ⊢
  dsimp only [support] at hs
  simp only [inner_add_left,inner_sub_left,real_inner_smul_left,inner_sub_right,norm_sub_sq_real,
    real_inner_self_eq_norm_sq] at h hs ⊢
  rw [real_inner_comm y x]
  nlinarith

variable [CompleteSpace E]

theorem hasGradientAt (x : E) : HasGradientAt D.potential (D.field x) x := by
  apply polyak.Interpolation.hasGradientAt_of_quadratic_sandwich
  · intro u v
    have h := D.potential_lower u v
    have hpos := mul_nonneg (show 0≤D.q/2 by linarith [D.q_pos]) (sq_nonneg ‖v-u‖)
    linarith
  · intro u v
    have h := D.potential_upper u v
    nlinarith [sq_nonneg ‖v-u‖]

theorem gradient_eq (x : E) : gradient D.potential x=D.field x := (D.hasGradientAt x).gradient

theorem smoothStronglyConvex : polyak.SmoothStronglyConvex D.q 1 D.potential where
  mu_pos := D.q_pos
  mu_lt_L := D.q_lt_one
  differentiable := fun x=>(D.hasGradientAt x).differentiableAt
  tangent_lower := fun x y=>by rw [D.gradient_eq];exact D.potential_lower x y
  grad_lipschitz := fun x y=>by rw [D.gradient_eq,D.gradient_eq,one_mul];exact D.field_lipschitz x y

end
end nesterov.Oracle.ExtensionData

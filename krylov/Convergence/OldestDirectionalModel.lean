import krylov.Convergence.OldestWindowSource
import krylov.Convergence.SlidingRFCAngle

/-!
Article: main_krylov, thm:Ip, correction-angle model action.
Use: retain the genuine perpendicular component in the oldest rank-one
model error, instead of bounding its action by the whole current error.
Source: the true oldest dual, exact rank-one congruence and inverse solves.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.LinearAlgebra krylov.Reference krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The true oldest rank-one model error only acts on the part of the
current error perpendicular to a direction annihilated by its actual dual. -/
theorem oldest_model_perpendicular_action
    (V X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (x d : EuclideanSpace ℝ (Fin (n+1))) (hd : inner ℝ (oldestDual V) d=0)
    {C : ℝ} (_hC : 0≤C) (hV : ‖V⁻¹‖≤C) :
    ‖cgOperator (inverseCongruence V X) x‖≤
      |X 0 0| *C^2*‖quadraticSearchPoint x d‖+
      C^2*‖X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖*‖x‖ := by
  let b := oldestDual V
  let R := X-X 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)
  have hb : ‖b‖≤C := (oldestDual_norm_le_inverse V).trans hV
  have hpair : inner ℝ b x=inner ℝ b (quadraticSearchPoint x d) := by
    simp only [quadraticSearchPoint,inner_sub_right,real_inner_smul_right,hd,mul_zero,sub_zero,b]
  have hsplit : cgOperator (inverseCongruence V X) x=
      (X 0 0*inner ℝ b x) • b+cgOperator (inverseCongruence V R) x := by
    rw [oldest_model_split V X]
    simp only [cgOperator,map_add,map_smul,_root_.add_apply,
      _root_.smul_apply,toEuclideanCLM_rankOne,InnerProductSpace.rankOne_apply,
      WithLp.toLp_ofLp,smul_smul,b,R]
  rw [hsplit]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_smul,Real.norm_eq_abs,abs_mul,hpair]
    have hp := abs_real_inner_le_norm b (quadraticSearchPoint x d)
    have hbp := pow_le_pow_left₀ (norm_nonneg b) hb 2
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (abs_nonneg (X 0 0))) (norm_nonneg b)
    have hs := mul_le_mul_of_nonneg_left hbp (show 0≤|X 0 0| *‖quadraticSearchPoint x d‖ by positivity)
    nlinarith only [hh,hs]
  · have hh := (cgOperator (inverseCongruence V R)).le_opNorm x
    simp only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] at hh
    apply hh.trans
    have ht := (inverseCongruence_norm V R).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hV 2) (norm_nonneg R))
    exact mul_le_mul_of_nonneg_right ht (norm_nonneg x)

/-- The genuine inverse-model query keeps its full actual model-error
vector, which permits the preceding angular gain to survive. -/
theorem secant_query_action_bound (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det)
    (x g : EuclideanSpace ℝ (Fin n)) :
    ‖x-cgOperator M⁻¹ g‖≤‖M⁻¹‖*(‖cgOperator (M-1) x‖+‖g-x‖) := by
  have hcancel : cgOperator M⁻¹ (cgOperator M x)=x := by
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) M⁻¹) ((Matrix.toEuclideanCLM (𝕜:=ℝ) M) x)=x
    rw [←mul_apply_eq_comp,←map_mul,Matrix.nonsing_inv_mul _ hM,map_one]
    rfl
  have he : x-cgOperator M⁻¹ g=cgOperator M⁻¹ (cgOperator (M-1) x-(g-x)) := by
    have hm : cgOperator (M-1) x=cgOperator M x-x := by
      simp only [cgOperator,map_sub,map_one,_root_.sub_apply,one_apply_eq_self]
    rw [hm,show cgOperator M x-x-(g-x)=cgOperator M x-g by abel_nf,map_sub,hcancel]
  rw [he]
  have hh := (cgOperator M⁻¹).le_opNorm (cgOperator (M-1) x-(g-x))
  simp only [cgOperator,Matrix.l2_opNorm_toEuclideanCLM] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))

end
end krylov.Convergence

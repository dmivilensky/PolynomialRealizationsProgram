import krylov.Functions.TrapezoidAffine

/-!
Article: main_krylov, condition (S) and thm:ss1F.
Use: bound the actual anchor remainder and the actual split coefficient.
Source: Euclidean orthogonal projection, actual covector annihilation, and
the midpoint/endpoint identity. No admissibility conclusion is a policy field.
-/

namespace krylov.Convergence
noncomputable section
open krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual offset left by a chosen split at the observed segment. -/
def splitRemainder (a s x : E) (l : ℝ) : E := x-(a+(1/2:ℝ) • s)-l • s

theorem splitRemainder_endpoint (a s x : E) (l : ℝ) :
    splitRemainder a s x l=(x-(a+s))-(l-1/2) • s := by
  dsimp only [splitRemainder]
  module

/-- The stated (S) condition also bounds the possibly large dimensionless
split coefficient in the only scaling that occurs in the remainder. -/
theorem split_half_deviation_bound (a s x : E) (l C : ℝ)
    (hw : ‖splitRemainder a s x l‖≤C*‖x-(a+s)‖) :
    |l-1/2| * ‖s‖≤(1+C)*‖x-(a+s)‖ := by
  have he : (l-1/2) • s=(x-(a+s))-splitRemainder a s x l := by
    rw [splitRemainder_endpoint]
    abel
  have hh := norm_sub_le (x-(a+s)) (splitRemainder a s x l)
  rw [←he,norm_smul,Real.norm_eq_abs] at hh
  calc
    _ ≤ ‖x-(a+s)‖+C*‖x-(a+s)‖ := hh.trans (add_le_add le_rfl hw)
    _ = _ := by ring

/-- The genuine Euclidean midpoint split satisfies (S) with constant one
in Euclidean canonical coordinates. -/
theorem innerSplit_admissible (a s x : E) (hs : s≠0) :
    ‖splitRemainder a s x (innerSplit a s x)‖≤‖x-(a+s)‖ := by
  let w := splitRemainder a s x (innerSplit a s x)
  let c := innerSplit a s x-1/2
  have hv : x-(a+s)=w+c • s := by
    rw [show w=(x-(a+s))-c • s from splitRemainder_endpoint a s x _]
    abel
  have ho : inner ℝ w s=0 := by
    rw [real_inner_comm]
    exact innerSplit_orthogonal a s x hs
  have hh := norm_add_sq_real w (c • s)
  rw [real_inner_smul_right,ho,mul_zero,mul_zero,add_zero,←hv] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith only [hh,sq_nonneg ‖c • s‖]

/-- The actual model-metric split is the endpoint oblique projection; its
observed covector annihilation is an exact data identity. -/
theorem covectorSplit_endpoint_annihilates (y : E →L[ℝ] ℝ) (a s x : E)
    (hy : y s≠0) : y (splitRemainder a s x (covectorSplit y a s x))=0 :=
  covectorSplit_annihilates y a s x hy

/-- An actual observed image close to its step makes the genuine model-metric
split satisfy (S) with a constant tending to one. This quantitative bound
needs no angle or split-regularity premise. -/
theorem covectorSplit_near_identity_admissible (a s x y : E) (hs : s≠0)
    {ε : ℝ} (hε : 0≤ε) (hε₁ : ε<1) (hy : ‖y-s‖≤ε*‖s‖) :
    0 < inner ℝ y s ∧
    ‖splitRemainder a s x (covectorSplit (innerSL ℝ y) a s x)‖≤
      ((1+ε)/(1-ε))*‖x-(a+s)‖ := by
  have hnorm : 0<‖s‖ := norm_pos_iff.mpr hs
  have hpair : |inner ℝ (y-s) s|≤ε*‖s‖^2 := by
    exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
      ((mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans_eq (by ring))
  have hys : 0 < inner ℝ y s := by
    have he : inner ℝ y s=‖s‖^2+inner ℝ (y-s) s := by
      rw [inner_sub_left,real_inner_self_eq_norm_sq]
      ring
    have hlo := (abs_le.mp hpair).1
    rw [he]
    have hp : 0<(1-ε)*‖s‖^2 := mul_pos (sub_pos.mpr hε₁) (sq_pos_of_pos hnorm)
    nlinarith only [hlo,hp]
  refine ⟨hys,?_⟩
  let w := splitRemainder a s x (covectorSplit (innerSL ℝ y) a s x)
  let v := x-(a+s)
  let c := covectorSplit (innerSL ℝ y) a s x-1/2
  have hv : v=w+c • s := by
    rw [show w=v-c • s from splitRemainder_endpoint a s x _]
    abel
  have ho : inner ℝ y w=0 := by
    change (innerSL ℝ y) (splitRemainder a s x (covectorSplit (innerSL ℝ y) a s x))=0
    exact covectorSplit_endpoint_annihilates (innerSL ℝ y) a s x hys.ne'
  have hwy : inner ℝ w y=0 := by rw [real_inner_comm]; exact ho
  have he : ‖w‖^2=inner ℝ w v-c*inner ℝ w s := by
    rw [hv,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    ring
  have hws : |inner ℝ w s|≤‖w‖*(ε*‖s‖) := by
    have hh : inner ℝ w s=inner ℝ w (s-y) := by rw [inner_sub_right,hwy,sub_zero]
    rw [hh]
    exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hy) (norm_nonneg _))
  have hc : |c| * ‖s‖≤‖v‖+‖w‖ := by
    have hcstep : v-w=c • s := by rw [hv]; abel
    have h := norm_sub_le v w
    rw [hcstep,norm_smul,Real.norm_eq_abs] at h
    exact h
  have hquad : ‖w‖^2≤‖w‖*‖v‖+ε*‖w‖*(‖v‖+‖w‖) := by
    have hab : -(c*inner ℝ w s)≤|c| * |inner ℝ w s| := by
      rw [←abs_mul]
      exact neg_le_abs _
    calc
      _ ≤ ‖w‖*‖v‖+|c| * |inner ℝ w s| := by
        rw [he]
        exact add_le_add (real_inner_le_norm _ _) hab
      _ ≤ ‖w‖*‖v‖+|c| * (‖w‖*(ε*‖s‖)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hws (abs_nonneg _))
      _ = ‖w‖*‖v‖+ε*‖w‖*(|c| * ‖s‖) := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (mul_nonneg hε (norm_nonneg _)))
  have hlin : (1-ε)*‖w‖≤(1+ε)*‖v‖ := by
    by_cases hw : w=0
    · simp only [hw,norm_zero,mul_zero]
      positivity
    · by_contra! hh
      have hp := mul_pos (norm_pos_iff.mpr hw) (sub_pos.mpr hh)
      nlinarith only [hquad,hp]
  change ‖w‖≤((1+ε)/(1-ε))*‖v‖
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr hε₁)).mpr (by simpa only [mul_comm] using hlin)

end
end krylov.Convergence

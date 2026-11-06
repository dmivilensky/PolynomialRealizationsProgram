import nesterov.Flow.Constants
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The exact constants and quadratic polynomial of the half-step layer. -/
namespace nesterov.Layer
noncomputable section

def Astar (θ y : ℝ) : ℝ := Real.sqrt (θ*(2-y)/y)
def Lambda (θ y A : ℝ) : ℝ := θ-y*(max A 0)^2/(2-y)
def constant (θ y A : ℝ) : ℝ := min (Flow.cQ θ y) (Lambda θ y A/3)
def polynomial (θ y c A φ : ℝ) : ℝ :=
  2*y*(θ-3*c)-4*A*y*φ+2*(2-y)*φ^2
def mixedPolynomial (θ y c A φ : ℝ) : ℝ :=
  2*y*(θ-2*c)-4*A*y*φ+2*(2-y)*φ^2

theorem Astar_pos {θ y : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    0<Astar θ y := Real.sqrt_pos.mpr (by positivity)

theorem Astar_sq {θ y : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    Astar θ y^2=θ*(2-y)/y := Real.sq_sqrt (by positivity)

theorem Lambda_le_theta {θ y A : ℝ} (hy : 0<y) (hy2 : y<2) :
    Lambda θ y A≤θ := by
  unfold Lambda
  exact sub_le_self _ (div_nonneg (mul_nonneg hy.le (sq_nonneg _)) (by linarith))

theorem Lambda_of_nonpos {θ y A : ℝ} (hA : A≤0) : Lambda θ y A=θ := by
  simp only [Lambda,max_eq_right hA,zero_pow (by omega : 2≠0),mul_zero,zero_div,sub_zero]

theorem constant_of_nonpos {θ y A : ℝ} (hA : A≤0) :
    constant θ y A=Flow.cF θ y := by
  rw [constant,Lambda_of_nonpos hA,Flow.cF,min_comm]

theorem Lambda_pos_iff {θ y A : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    0<Lambda θ y A ↔ A<Astar θ y := by
  have hs := Real.sq_sqrt (show 0≤θ*(2-y)/y by positivity)
  have hp := Astar_pos hθ hy hy2
  have hden : 0<2-y := by linarith
  have hsq : Astar θ y^2=θ*(2-y)/y := hs
  constructor
  · intro h
    by_cases hA : A≤0
    · exact hA.trans_lt hp
    · have hAp : 0<A := lt_of_not_ge hA
      rw [Lambda,max_eq_left hAp.le] at h
      have hh := (div_lt_iff₀ hden).mp (show y*A^2/(2-y)<θ by linarith)
      have heq : y*Astar θ y^2=θ*(2-y) := by rw [hsq];field_simp
      by_contra hn
      have hle : Astar θ y≤A := le_of_not_gt hn
      have hss : Astar θ y^2≤A^2 := (sq_le_sq₀ hp.le hAp.le).mpr hle
      have hm := mul_le_mul_of_nonneg_left hss hy.le
      linarith
  · intro h
    by_cases hA : A≤0
    · rw [Lambda_of_nonpos hA];exact hθ
    · have hAp : 0<A := lt_of_not_ge hA
      have hlt : A^2<Astar θ y^2 := by nlinarith
      have hh := mul_lt_mul_of_pos_left hlt hy
      have heq : y*Astar θ y^2=θ*(2-y) := by rw [hsq];field_simp
      rw [Lambda,max_eq_left hAp.le]
      have hd := (div_lt_iff₀ hden).mpr (show y*A^2<θ*(2-y) by linarith)
      linarith

theorem polynomial_minimum {θ y c A : ℝ} (hy2 : y<2) :
    polynomial θ y c A (A*y/(2-y))=
      (2*y/(2-y))*((θ-3*c)*(2-y)-y*A^2) := by
  unfold polynomial
  field_simp [show 2-y≠0 by linarith]
  ring

theorem mixedPolynomial_minimum {θ y c A : ℝ} (hy2 : y<2) :
    mixedPolynomial θ y c A (A*y/(2-y))=
      (2*y/(2-y))*((θ-2*c)*(2-y)-y*A^2) := by
  unfold mixedPolynomial
  field_simp [show 2-y≠0 by linarith]
  ring

theorem constant_pos_iff {θ y A : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    0<constant θ y A ↔ A<Astar θ y := by
  rw [constant,lt_min_iff]
  constructor
  · intro h
    apply (Lambda_pos_iff hθ hy hy2).mp
    linarith [h.2]
  · intro h
    exact ⟨Flow.cQ_pos hθ hy,div_pos ((Lambda_pos_iff hθ hy hy2).mpr h) (by norm_num)⟩

theorem polynomial_min_neg {θ y c A : ℝ} (hy : 0<y) (hy2 : y<2) (hA : 0<A)
    (hc : max (Lambda θ y A) 0/3<c) : polynomial θ y c A (A*y/(2-y))<0 := by
  have hcl : Lambda θ y A<3*c := by linarith [le_max_left (Lambda θ y A) 0]
  have hd : 0<2-y := by linarith
  have hh : (θ-3*c)*(2-y)<y*A^2 := by
    rw [Lambda,max_eq_left hA.le] at hcl
    exact (lt_div_iff₀ hd).mp (show θ-3*c<y*A^2/(2-y) by linarith)
  rw [polynomial_minimum hy2]
  exact mul_neg_of_pos_of_neg (div_pos (by positivity) hd) (by linarith)

theorem mixedPolynomial_min_neg {θ y c A : ℝ} (hy : 0<y) (hy2 : y<2) (hA : 0<A)
    (hc : max (Lambda θ y A) 0/2<c) : mixedPolynomial θ y c A (A*y/(2-y))<0 := by
  have hcl : Lambda θ y A<2*c := by linarith [le_max_left (Lambda θ y A) 0]
  have hd : 0<2-y := by linarith
  have hh : (θ-2*c)*(2-y)<y*A^2 := by
    rw [Lambda,max_eq_left hA.le] at hcl
    exact (lt_div_iff₀ hd).mp (show θ-2*c<y*A^2/(2-y) by linarith)
  rw [mixedPolynomial_minimum hy2]
  exact mul_neg_of_pos_of_neg (div_pos (by positivity) hd) (by linarith)

theorem continuous_Lambda (θ y : ℝ) : Continuous (Lambda θ y) := by
  unfold Lambda
  fun_prop

theorem continuous_constant (θ y : ℝ) : Continuous (constant θ y) := by
  unfold constant
  exact continuous_const.min ((continuous_Lambda θ y).div_const 3)

theorem Lambda_antitone {θ y : ℝ} (hy : 0<y) (hy2 : y<2) : Antitone (Lambda θ y) := by
  intro A B hAB
  have hm : max A 0≤max B 0 := max_le_max hAB le_rfl
  have hs := (sq_le_sq₀ (le_max_right A 0) (le_max_right B 0)).mpr hm
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hy.le)
    (show 0≤2-y by linarith)
  unfold Lambda
  linarith

theorem constant_antitone {θ y : ℝ} (hy : 0<y) (hy2 : y<2) : Antitone (constant θ y) := by
  intro A B hAB
  exact min_le_min_left _ (div_le_div_of_nonneg_right (Lambda_antitone hy hy2 hAB) (by norm_num))

theorem Lambda_at_Astar {θ y : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    Lambda θ y (Astar θ y)=0 := by
  rw [Lambda,max_eq_left (Astar_pos hθ hy hy2).le,Astar_sq hθ hy hy2]
  field_simp [hy.ne',show 2-y≠0 by linarith]
  ring

theorem constant_at_Astar {θ y : ℝ} (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) :
    constant θ y (Astar θ y)=0 := by
  rw [constant,Lambda_at_Astar hθ hy hy2,zero_div,min_eq_right (Flow.cQ_pos hθ hy).le]

theorem constant_plateau {θ y A : ℝ} (hy : 0<y) (hy2 : y<2)
    (h : 3*Flow.cF θ y≤Lambda θ y A) : constant θ y A=Flow.cF θ y := by
  apply le_antisymm
  · have hh := min_le_min_left (Flow.cQ θ y)
      (div_le_div_of_nonneg_right (Lambda_le_theta (θ:=θ) (A:=A) hy hy2) (by norm_num : (0:ℝ)≤3))
    simpa only [constant,Flow.cF,min_comm] using hh
  · exact le_min (min_le_right _ _) (by linarith)

theorem constant_two_one (A : ℝ) : constant 2 1 A=(2-(max A 0)^2)/3 := by
  norm_num [constant,Lambda,Flow.cQ]
  nlinarith [sq_nonneg (max A 0)]

@[simp] theorem Astar_two_one : Astar 2 1=Real.sqrt 2 := by norm_num [Astar]

end
end nesterov.Layer

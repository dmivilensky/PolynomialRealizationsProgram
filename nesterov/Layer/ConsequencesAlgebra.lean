import nesterov.Layer.Constants

/-! The source's layer plateau, monotonicity, sixth-order coefficient and
exact plotted example. Algebraic definitions beyond Astar are not assertions
of an accelerated rate; the figure domain is stated explicitly below. -/
namespace nesterov.Layer
noncomputable section
open Set

theorem constant_le_flow {θ y A : ℝ} (hy : 0<y) (hy2 : y<2) :
    constant θ y A≤Flow.cF θ y := by
  rw [constant,Flow.cF]
  exact le_min ((min_le_right _ _).trans (div_le_div_of_nonneg_right
    (Lambda_le_theta hy hy2) (by norm_num))) (min_le_left _ _)

theorem constant_eq_flow_iff {θ y A : ℝ} (hy : 0<y) (hy2 : y<2) :
    constant θ y A=Flow.cF θ y ↔ 3*Flow.cF θ y≤Lambda θ y A := by
  constructor
  · intro h
    have hh : Flow.cF θ y≤Lambda θ y A/3 := by
      rw [←h]
      exact min_le_right _ _
    linarith
  · intro h
    apply le_antisymm (constant_le_flow hy hy2)
    exact le_min (Flow.cF_le_cQ θ y) (by linarith)

def s6 (y : ℝ) : ℝ := (2-y)/(4*y^2)

theorem s6_pos {y : ℝ} (hy : 0<y) (hy2 : y<2) : 0<s6 y := by
  exact div_pos (by linarith) (mul_pos (by norm_num) (sq_pos_of_pos hy))

theorem Lambda_s6 {θ y A : ℝ} (hy2 : y<2) :
    Lambda θ y A=θ-(max A 0)^2/(4*y*s6 y) := by
  unfold Lambda s6
  field_simp [show 2-y≠0 by linarith]

theorem Astar_s6 {θ y : ℝ} (hy : 0<y) : Astar θ y=2*Real.sqrt (θ*y*s6 y) := by
  have he : θ*(2-y)/y=4*(θ*y*s6 y) := by
    unfold s6
    field_simp [hy.ne']
  rw [Astar,he,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num

def vertex (y A : ℝ) : ℝ := max A 0*y/(2-y)

theorem polynomial_completed_square {θ y c A φ : ℝ} (hy2 : y<2) (hA : 0≤A) :
    polynomial θ y c A φ=
      2*y*(Lambda θ y A-3*c)+2*(2-y)*(φ-A*y/(2-y))^2 := by
  unfold polynomial Lambda
  rw [max_eq_left hA]
  field_simp [show 2-y≠0 by linarith]
  ring

theorem polynomial_minimum_on_nonneg {θ y c A : ℝ} (hy : 0<y) (hy2 : y<2) :
    0≤vertex y A ∧ polynomial θ y c A (vertex y A)=2*y*(Lambda θ y A-3*c) ∧
      ∀ φ : ℝ,0≤φ → polynomial θ y c A (vertex y A)≤polynomial θ y c A φ := by
  have hv : 0≤vertex y A := div_nonneg (mul_nonneg (le_max_right A 0) hy.le) (by linarith)
  refine ⟨hv,?_,?_⟩
  · by_cases hA : A≤0
    · simp only [vertex,max_eq_right hA,zero_mul,zero_div,polynomial,mul_zero,zero_pow (by omega : 2≠0),
        sub_zero,add_zero,Lambda_of_nonpos hA]
    · have hp := polynomial_completed_square (θ:=θ) (y:=y) (c:=c) (A:=A)
        (φ:=vertex y A) hy2 (le_of_not_ge hA)
      simpa only [vertex,max_eq_left (le_of_not_ge hA),sub_self,zero_pow (by omega : 2≠0),mul_zero,add_zero] using hp
  · intro φ hφ
    by_cases hA : A≤0
    · have hlinear : 0≤ -4*A*y*φ := mul_nonneg (by nlinarith) hφ
      have hquad : 0≤2*(2-y)*φ^2 := by positivity
      simp only [vertex,max_eq_right hA,zero_mul,zero_div,polynomial,mul_zero,zero_pow (by omega : 2≠0),sub_zero,add_zero]
      linarith
    · rw [polynomial_completed_square hy2 (le_of_not_ge hA),
        polynomial_completed_square hy2 (le_of_not_ge hA)]
      simp only [vertex,max_eq_left (le_of_not_ge hA),sub_self,zero_pow (by omega : 2≠0),mul_zero,add_zero]
      exact le_add_of_nonneg_right (by positivity)

theorem polynomial_threshold_square {θ y A φ : ℝ} (hy2 : y<2) (hA : 0≤A) :
    polynomial θ y (Lambda θ y A/3) A φ=2*(2-y)*(φ-A*y/(2-y))^2 := by
  rw [polynomial_completed_square hy2 hA]
  ring

def mixedConstant (θ y A : ℝ) : ℝ :=
  min (Flow.cF θ y) (max (Lambda θ y A) 0/2)

theorem constant_le_mixedConstant {θ y A : ℝ} (hy : 0<y) (hy2 : y<2) :
    constant θ y A≤mixedConstant θ y A := by
  apply le_min (constant_le_flow hy hy2)
  have h : constant θ y A≤Lambda θ y A/3 := min_le_right _ _
  have hm := le_max_left (Lambda θ y A) 0
  have hp := le_max_right (Lambda θ y A) 0
  change constant θ y A≤max (Lambda θ y A) 0/2
  linarith

theorem figure_base_constants :
    Flow.cQ 2 1=1 ∧ Flow.cF 2 1=2/3 ∧ Astar 2 1=Real.sqrt 2 := by
  norm_num [Flow.cQ,Flow.cF,Astar]

theorem figure_Lambda (A : ℝ) : Lambda 2 1 A=2-(max A 0)^2 := by
  norm_num [Lambda]

theorem figure_constant (A : ℝ) : constant 2 1 A=(2-(max A 0)^2)/3 :=
  constant_two_one A

theorem figure_solid_domain {A : ℝ} (hA : A≤Real.sqrt 2) :
    0≤constant 2 1 A ∧ constant 2 1 A≤2/3 := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hmax : max A 0≤Real.sqrt 2 := max_le hA (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ (le_max_right A 0) (Real.sqrt_nonneg _)).mpr hmax
  rw [figure_constant]
  constructor <;> nlinarith [sq_nonneg (max A 0)]

theorem figure_mixed_domain {A : ℝ} (hA0 : 0≤A) (hA : A≤Real.sqrt 2) :
    mixedConstant 2 1 A=min (2/3) ((2-A^2)/2) := by
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hsq := (sq_le_sq₀ hA0 (Real.sqrt_nonneg _)).mpr hA
  rw [mixedConstant,figure_base_constants.2.1,figure_Lambda,max_eq_left hA0,
    max_eq_left (by linarith : 0≤2-A^2)]

end
end nesterov.Layer

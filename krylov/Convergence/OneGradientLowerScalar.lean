import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, thm:LB, uniform common-output lower bound.
Use: control every possible common final output of the two actual cubic
sources; no a priori output localization is needed. A large output error
already satisfies the lower bound, while a smaller one controls the exact
quadratic hidden-coordinate product by its real displacement.
Source: Appendix G's v plus/minus w argument and the scalar triangle inequality.
-/
namespace krylov.Convergence
noncomputable section

/-- Either sign of a true opposite perturbation detects both the common
part and the hidden part, in every normed space. Article: thm:LB. -/
theorem opposite_outputs_norm_lower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v w : E) : ‖v‖≤max ‖v+w‖ ‖v-w‖ ∧‖w‖≤max ‖v+w‖ ‖v-w‖ := by
  have hv : (2:ℝ) • v=(v+w)+(v-w) := by module
  have hw : (2:ℝ) • w=(v+w)-(v-w) := by module
  have hav := norm_add_le (v+w) (v-w)
  have haw := norm_sub_le (v+w) (v-w)
  rw [←hv,norm_smul,show ‖(2:ℝ)‖=2 by norm_num] at hav
  rw [←hw,norm_smul,show ‖(2:ℝ)‖=2 by norm_num] at haw
  have hl := le_max_left ‖v+w‖ ‖v-w‖
  have hr := le_max_right ‖v+w‖ ‖v-w‖
  constructor <;> linarith only [hav,haw,hl,hr]

/-- Perturbing both factors in the actual hidden-coordinate product has
this exact uniform error bound. Article: main_krylov, thm:LB. -/
theorem hidden_product_comparison (z y p : ℝ) :
    |y| *|y-p|≤|z| *|z-p|+|z-y| *(|y|+|y-p|+|z-y|) := by
  have he : y*(y-p)=z*(z-p)-(z-y)*y-(z-y)*(y-p)-(z-y)^2 := by ring
  rw [←abs_mul,he]
  calc
    _ ≤ |z*(z-p)-(z-y)*y-(z-y)*(y-p)|+|(z-y)^2| := abs_sub _ _
    _ ≤ (|z*(z-p)-(z-y)*y|+|(z-y)*(y-p)|)+|(z-y)^2| :=
      by
        gcongr
        exact abs_sub _ _
    _ ≤ ((|z*(z-p)|+|(z-y)*y|)+|(z-y)*(y-p)|)+|(z-y)^2| :=
      by
        gcongr
        exact abs_sub _ _
    _ = _ := by simp only [abs_mul,abs_pow];ring

/-- Every common output has the original cubic two-source lower bound,
with the explicit relative perturbation denominator, regardless of how
far the method chose to place it. Article: main_krylov, thm:LB. -/
theorem hidden_product_output_lower
    (a c R z y p : ℝ) (ha : 0≤a) (hc : 0≤c) (hR : 0≤R)
    (hvalue : a*|z| *|z-p|≤R) (hcoordinate : |z-y|≤c*R) :
    let T := a*|y| *|y-p|
    let η := a*c*(|y|+|y-p|+c*T)
    T/(1+η)≤R := by
  let T := a*|y| *|y-p|
  let η := a*c*(|y|+|y-p|+c*T)
  have hT : 0≤T := by dsimp only [T];positivity
  have hη : 0≤η := by dsimp only [η];positivity
  change T/(1+η)≤R
  by_cases hlarge : T≤R
  · exact (div_le_self hT (by linarith only [hη] : 1≤1+η)).trans hlarge
  · have hsmall : R≤T := (le_of_not_ge hlarge)
    have hd : |z-y|≤c*T := hcoordinate.trans (mul_le_mul_of_nonneg_left hsmall hc)
    have hp := mul_le_mul_of_nonneg_left (hidden_product_comparison z y p) ha
    have hterm : a*(|z-y| *(|y|+|y-p|+|z-y|))≤η*R := by
      calc
        _ ≤ a*((c*R)*(|y|+|y-p|+c*T)) := by gcongr
        _ = η*R := by dsimp only [η];ring
    have hbound : T≤R+η*R := by
      dsimp only [T]
      nlinarith only [hp,hterm,hvalue]
    exact (div_le_iff₀ (by linarith only [hη] : 0<1+η)).mpr (by nlinarith only [hbound])

end
end krylov.Convergence

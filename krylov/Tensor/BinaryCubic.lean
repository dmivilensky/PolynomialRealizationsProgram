import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
Article: main_krylov, apD:lem-binary and thm:Fplanar.
Use: the actual binary cubic ball and its exact coefficient symmetries.
Source: homogeneous binary cubic algebra; the unit circle formulation is
proved equivalent to the angular definition in the article.
-/

namespace krylov.Tensor
noncomputable section

/-- The four coefficients of a symmetric binary cubic, with binomial factors
in its diagonal polynomial. Article: main_krylov, apD:lem-binary. -/
structure BinaryCubic where
  t0 : ℝ
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ
  deriving DecidableEq

namespace BinaryCubic

/-- The genuine diagonal polynomial, rather than an assumed tensor bound.
Article: main_krylov, apD:lem-binary, definition of K. -/
def eval (t : BinaryCubic) (c s : ℝ) : ℝ :=
  t.t0*c^3 + 3*t.t1*c^2*s + 3*t.t2*c*s^2 + t.t3*s^3

/-- The actual unit ball in the diagonal cubic norm.
Article: main_krylov, apD:lem-binary. -/
def InBall (t : BinaryCubic) : Prop :=
  ∀ c s : ℝ, c^2+s^2=1 → |t.eval c s|≤1

/-- Every point of the real unit circle has an angular parametrization.
Article: main_krylov, apD:lem-binary, equivalence of circle and angle domains.
Proof: arccos gives the upper semicircle; reflection gives the lower one. -/
theorem exists_angle (c s : ℝ) (h : c^2+s^2=1) :
    ∃ φ : ℝ, Real.cos φ=c ∧ Real.sin φ=s := by
  have hc : -1≤c ∧ c≤1 := by constructor <;> nlinarith [sq_nonneg s]
  have hs : Real.sqrt (1-c^2)=|s| := by
    rw [show 1-c^2=s^2 by linarith, Real.sqrt_sq_eq_abs]
  by_cases hsign : 0≤s
  · refine ⟨Real.arccos c,Real.cos_arccos hc.1 hc.2,?_⟩
    rw [Real.sin_arccos,hs,abs_of_nonneg hsign]
  · refine ⟨-Real.arccos c,?_,?_⟩
    · rw [Real.cos_neg,Real.cos_arccos hc.1 hc.2]
    · rw [Real.sin_neg,Real.sin_arccos,hs,abs_of_neg (lt_of_not_ge hsign),neg_neg]

/-- The actual ball agrees with the angular sup-norm condition in the paper.
Article: main_krylov, apD:lem-binary. -/
theorem inBall_iff_angle (t : BinaryCubic) :
    t.InBall ↔ ∀ φ : ℝ, |t.eval (Real.cos φ) (Real.sin φ)|≤1 := by
  constructor
  · intro h φ
    exact h _ _ (by nlinarith [Real.sin_sq_add_cos_sq φ])
  · intro h c s hcs
    obtain ⟨φ,rfl,rfl⟩ := exists_angle c s hcs
    exact h φ

/-- Negating all coefficients negates the cubic, preserving its true ball.
Article: main_krylov, apD:lem-binary(b). -/
def neg (t : BinaryCubic) : BinaryCubic := ⟨-t.t0,-t.t1,-t.t2,-t.t3⟩

/-- Negation is a symmetry of the genuine binary cubic unit ball.
Article: main_krylov, apD:lem-binary(b). -/
theorem inBall_neg {t : BinaryCubic} (h : t.InBall) : t.neg.InBall := by
  intro c s hcs
  have he : t.neg.eval c s=-(t.eval c s) := by simp only [eval,neg];ring
  rw [he,abs_neg]
  exact h c s hcs

/-- Reflection in the second coordinate changes precisely the odd coefficients.
Article: main_krylov, apD:lem-binary(c). -/
theorem inBall_reflect_second {t : BinaryCubic} (h : t.InBall) :
    (⟨t.t0,-t.t1,t.t2,-t.t3⟩ : BinaryCubic).InBall := by
  intro c s hcs
  have he : (⟨t.t0,-t.t1,t.t2,-t.t3⟩ : BinaryCubic).eval c s=t.eval c (-s) := by
    simp only [eval];ring
  rw [he]
  exact h c (-s) (by nlinarith)

/-- Reflection in the first coordinate changes precisely the even coefficients.
Article: main_krylov, apD:lem-binary(c). -/
theorem inBall_reflect_first {t : BinaryCubic} (h : t.InBall) :
    (⟨-t.t0,t.t1,-t.t2,t.t3⟩ : BinaryCubic).InBall := by
  intro c s hcs
  have he : (⟨-t.t0,t.t1,-t.t2,t.t3⟩ : BinaryCubic).eval c s=t.eval (-c) s := by
    simp only [eval];ring
  rw [he]
  exact h (-c) s (by nlinarith)

/-- Each pure coefficient is bounded by testing the corresponding circle axis.
Article: main_krylov, apD:lem-binary, elementary endpoint coefficients. -/
theorem axis_bounds {t : BinaryCubic} (h : t.InBall) : |t.t0|≤1 ∧ |t.t3|≤1 := by
  constructor
  · simpa [eval] using h 1 0 (by norm_num)
  · simpa [eval] using h 0 1 (by norm_num)

end BinaryCubic
end
end krylov.Tensor

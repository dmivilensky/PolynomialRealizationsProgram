import polyak.Spectral.Feasibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Article: Lemma dualfactor, positivity of the Chebyshev divided differences.
Use: every quotient extends polynomially to the corner G=c=1.
Proof: exact division by X−G; at the diagonal the quotient is the polynomial
derivative. Bounds off the diagonal follow from the extremal Chebyshev bounds.
-/

noncomputable section
namespace polyak.Boundary
open Spectral Polynomial

/-- Article: the polynomial continuation of (p(G)−p(c))/(G−c). -/
def dividedPolynomial (p : ℝ[X]) (G : ℝ) : ℝ[X] := p /ₘ (X-C G)

/-- Article: divided-difference evaluation, including the coincident endpoints. -/
def divided (p : ℝ[X]) (G c : ℝ) : ℝ := (dividedPolynomial p G).eval c

/-- Article: exact factor theorem for the divided polynomial. -/
theorem divided_factor (p : ℝ[X]) (G c : ℝ) :
    (G-c)*divided p G c = p.eval G-p.eval c := by
  have h := congrArg (Polynomial.eval c) (X_sub_C_mul_divByMonic_eq_sub_modByMonic p G)
  simp only [eval_mul,eval_sub,eval_X,eval_C,modByMonic_X_sub_C_eq_C_eval] at h
  dsimp [divided,dividedPolynomial]
  nlinarith

/-- Article: the divided polynomial agrees with the derivative at the diagonal. -/
theorem divided_self (p : ℝ[X]) (G : ℝ) : divided p G G = p.derivative.eval G := by
  have h := congrArg (Polynomial.eval G)
    (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p G)
  simpa [divided,dividedPolynomial] using h

/-- Article: Tₙ(G)≥1 beyond the frequency interval. -/
theorem one_le_chebT (n : ℕ) {G : ℝ} (hG : 1 ≤ G) : 1 ≤ chebT n G :=
  Polynomial.Chebyshev.one_le_eval_T_real _ hG

/-- Article: Tₙ(c)≤1 throughout the frequency interval. -/
theorem chebT_le_one (n : ℕ) (c : Frequency) : chebT n c ≤ 1 := by
  rw [← Real.cos_arccos c.property.1 c.property.2,chebT_cos]
  exact Real.cos_le_one _

/-- Article: the two-step positive expansion of U in first-kind Chebyshev polynomials. -/
theorem chebU_add_two (n : ℕ) (x : ℝ) : chebU (n+2) x = 2*chebT (n+2) x+chebU n x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.Chebyshev.U_eq_two_mul_T_add_U ℝ (n : ℤ))
  simpa [chebU,chebT] using h

/-- Article: Uₙ(G)≥n+1 for G≥1; in particular every lag denominator is positive. -/
theorem degree_le_chebU (n : ℕ) {G : ℝ} (hG : 1 ≤ G) : (n : ℝ)+1 ≤ chebU n G := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebU]
  | one => simp only [chebU, Nat.cast_one, Polynomial.Chebyshev.U_one, eval_mul,eval_ofNat,eval_X]; linarith
  | more n ih _ =>
    rw [chebU_add_two]
    have ht := one_le_chebT (n+2) hG
    push_cast
    linarith

/-- Article: Uₙ(c)≤n+1 on the full frequency interval, including its endpoints. -/
theorem chebU_le_degree (n : ℕ) (c : Frequency) : chebU n c ≤ (n : ℝ)+1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebU]
  | one => simp only [chebU,Nat.cast_one,Polynomial.Chebyshev.U_one,eval_mul,eval_ofNat,eval_X]; linarith [c.property.2]
  | more n ih _ =>
    rw [chebU_add_two]
    have ht := chebT_le_one (n+2) c
    push_cast
    linarith

/-- Article: positivity of T's divided difference throughout G≥1≥c. -/
theorem divided_T_nonneg (n : ℕ) {G : ℝ} (hG : 1 ≤ G) (c : Frequency) :
    0 ≤ divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c := by
  by_cases heq : G=(c : ℝ)
  · have h1 : G=1 := by linarith [c.property.2]
    have hc : (c : ℝ)=1 := by linarith
    rw [h1,hc,divided_self,Polynomial.Chebyshev.derivative_T_eval_one]
    positivity
  · have hgap : 0 < G-(c : ℝ) :=
      sub_pos.mpr (lt_of_le_of_ne (c.property.2.trans hG) (Ne.symm heq))
    have h := divided_factor (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c
    have ht := (chebT_le_one n c).trans (one_le_chebT n hG)
    change (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (c : ℝ) ≤
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval G at ht
    nlinarith

/-- Article: positivity of U's divided difference throughout G≥1≥c. -/
theorem divided_U_nonneg (n : ℕ) {G : ℝ} (hG : 1 ≤ G) (c : Frequency) :
    0 ≤ divided (Polynomial.Chebyshev.U ℝ (n : ℤ)) G c := by
  by_cases heq : G=(c : ℝ)
  · have h1 : G=1 := by linarith [c.property.2]
    have hc : (c : ℝ)=1 := by linarith
    rw [h1,hc,divided_self,Polynomial.Chebyshev.derivative_U_eval_one_eq_div]
    positivity
  · have hgap : 0 < G-(c : ℝ) :=
      sub_pos.mpr (lt_of_le_of_ne (c.property.2.trans hG) (Ne.symm heq))
    have h := divided_factor (Polynomial.Chebyshev.U ℝ (n : ℤ)) G c
    have ht := (chebU_le_degree n c).trans (degree_le_chebU n hG)
    change (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (c : ℝ) ≤
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval G at ht
    nlinarith

end polyak.Boundary

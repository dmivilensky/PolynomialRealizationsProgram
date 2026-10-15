import «2610.05164v2».DualCertificate.PolynomialPotential
import «2610.05164v2».DualCertificate.Coordinate
import Mathlib.Algebra.Polynomial.Div

/-!
Article: 2610.05164v2, Lemma 16.
F.1: every printed D(P) is a genuine polynomial quotient.
Result: `«2610.05164v2».DualCertificate.moment_coefficient_divisibility` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Polynomial Set
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `Side.divisor` by pattern matching with result type `Side → Polynomial ℚ`. The
displayed branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».DualCertificate.Side.divisor_value` rewrites with this definition to
establish exact identity `aeval (side.q t) side.divisor=t^3`.

Article: 2610.05164v2, Lemma 16 via
`«2610.05164v2».DualCertificate.monomial_coefficient_divisibility`.
-/
def Side.divisor : Side → Polynomial ℚ
  | .left => X
  | .right => C 2-X

/--
Defines `Side.polynomialQuotient` of type `Polynomial ℚ` by `match side with | .left => P /ₘ X
| .right => -(P /ₘ (X-C 2))`.

Use: `«2610.05164v2».DualCertificate.Side.polynomialQuotient_factor` rewrites with this
definition to establish the identity `side.divisor*side.polynomialQuotient P=P`.

Article: 2610.05164v2, Lemma 16.
-/
def Side.polynomialQuotient (side : Side) (P : Polynomial ℚ) : Polynomial ℚ := match side with
  | .left => P /ₘ X
  | .right => -(P /ₘ (X-C 2))

/--
Exact identity `side.divisor*side.polynomialQuotient P=P`.

Use: `«2610.05164v2».DualCertificate.Side.polynomialQuotient_value` uses this identity to
establish exact identity `t^3*aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P`.

Article: 2610.05164v2, Lemma 16.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Side.polynomialQuotient_factor (side : Side) {P : Polynomial ℚ}
    (hP : side.divisor∣P) : side.divisor*side.polynomialQuotient P=P := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  obtain ⟨A,rfl⟩ := hP
  cases side with
  | left => simp [Side.divisor,Side.polynomialQuotient,mul_divByMonic_cancel_left,monic_X]
  | right =>
    have he : (C 2-X)*A=(X-C 2)*(-A) := by ring
    rw [Side.polynomialQuotient,Side.divisor,he,mul_divByMonic_cancel_left _ (monic_X_sub_C 2)]
    ring

/--
Exact identity `aeval (side.q t) side.divisor=t^3`.

Use: `«2610.05164v2».DualCertificate.Side.polynomialQuotient_value` uses this identity to
establish exact identity `t^3*aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P`.

Article: 2610.05164v2, Lemma 16.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Side.divisor_value (side : Side) (t : ℝ) :
    aeval (side.q t) side.divisor=t^3 := by cases side <;> simp [Side.divisor,Side.q]

/--
Exact identity `t^3*aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P`.

Use: `«2610.05164v2».DualCertificate.Side.polynomialQuotient_division` uses this identity to
establish exact identity `aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P/t^3`.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Side.divisor_value`,
`«2610.05164v2».DualCertificate.Side.polynomialQuotient_factor` with the arguments shown in the
proof.
-/
theorem Side.polynomialQuotient_value (side : Side) {P : Polynomial ℚ}
    (hP : side.divisor∣P) (t : ℝ) :
    t^3*aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P := by rw [← side.divisor_value t,← map_mul,side.polynomialQuotient_factor hP]

/--
Exact identity `aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P/t^3`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.Side.polynomialQuotient_value` with the arguments shown in the
proof.
-/
theorem Side.polynomialQuotient_division (side : Side) {P : Polynomial ℚ}
    (hP : side.divisor∣P) {t : ℝ} (ht : t≠0) :
    aeval (side.q t) (side.polynomialQuotient P)=aeval (side.q t) P/t^3 := by
  apply (eq_div_iff (pow_ne_zero _ ht)).mpr
  simpa only [mul_comm] using side.polynomialQuotient_value hP t

/--
Smoothness to the stated order: `ContDiff ℝ ∞ (fun t : ℝ => aeval (side.q t)
(side.polynomialQuotient P))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 16.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Side.polynomialQuotient_smooth (side : Side) (P : Polynomial ℚ) :
    ContDiff ℝ ∞ (fun t : ℝ => aeval (side.q t) (side.polynomialQuotient P)) := by
  apply (side.polynomialQuotient P).contDiff_aeval ∞ |>.comp
  cases side <;> unfold Side.q <;> fun_prop

/--
All monomial terms of positive state degree have the six divisibilities used in (49). The
exceptional linear degree carries the printed extra q.

Establishes the uniform, quantified assertion `∀ side : Side, side.divisor∣P.derivative*X^l ∧
side.divisor∣P*X^(l-1) ∧ side.divisor∣P*X^l ∧ side.divisor∣P*X^(l+1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 16.

Proof: Separate `l=1` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem monomial_coefficient_divisibility {P : Polynomial ℚ} {l : ℕ}
    (hl : 1≤l) (hr : (C 2-X)^2∣P) (hlinear : l=1 → X∣P) :
    ∀ side : Side, side.divisor∣P.derivative*X^l ∧
      side.divisor∣P*X^(l-1) ∧ side.divisor∣P*X^l ∧ side.divisor∣P*X^(l+1) := by
  -- Separate `l=1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hright : C 2-X∣P := (dvd_pow_self _ (by norm_num : (2:ℕ)≠0)).trans hr
  have hdright : C 2-X∣P.derivative := by
    simpa using (pow_sub_one_dvd_derivative_of_pow_dvd hr)
  have hXl : (X : Polynomial ℚ)∣X^l := dvd_pow_self _ (by omega)
  have hXm : (X : Polynomial ℚ)∣P*X^(l-1) := by
    by_cases he : l=1
    · exact dvd_mul_of_dvd_left (hlinear he) _
    · exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
  intro side
  cases side with
  | left => exact ⟨dvd_mul_of_dvd_right hXl _,hXm,
      dvd_mul_of_dvd_right hXl _,dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _⟩
  | right => exact ⟨dvd_mul_of_dvd_left hdright _,dvd_mul_of_dvd_left hright _,
      dvd_mul_of_dvd_left hright _,dvd_mul_of_dvd_left hright _⟩

/--
The h term has the two divisibilities in (48).

Establishes the uniform, quantified assertion `∀ side : Side, side.divisor∣P.derivative*X ∧
side.divisor∣P*X`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Lemma 16.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem moment_coefficient_divisibility {P : Polynomial ℚ} (hr : (C 2-X)^2∣P) :
    ∀ side : Side, side.divisor∣P.derivative*X ∧ side.divisor∣P*X := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hright : C 2-X∣P := (dvd_pow_self _ (by norm_num : (2:ℕ)≠0)).trans hr
  have hdright : C 2-X∣P.derivative := by
    simpa using (pow_sub_one_dvd_derivative_of_pow_dvd hr)
  intro side
  cases side with
  | left => exact ⟨dvd_mul_left _ _,dvd_mul_left _ _⟩
  | right => exact ⟨dvd_mul_of_dvd_left hdright _,dvd_mul_of_dvd_left hright _⟩

end
end «2610.05164v2».DualCertificate

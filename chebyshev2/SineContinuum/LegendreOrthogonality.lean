import chebyshev2.SineContinuum.LegendrePolynomials
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
Article: chebyshev2, Proposition 2.
Orthogonality of the actual community Legendre polynomials, obtained from their Sturm equation and a
boundary flux that vanishes at both ends.
Use: `chebyshev2.SineContinuum.legendre_ode` feeds
`chebyshev2.SineContinuum.upsilon_explicit_ode` (The genuine second derivative solves Lemma 5's
singular equation with the exact printed eigenvalue).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Polynomial Set Real MeasureTheory
set_option backward.isDefEq.respectTransparency false

/--
Defines `legendreValue` of type `ℝ` by `(shifted n).eval x`.

Use: `chebyshev2.SineContinuum.legendre_orthogonal` rewrites with this definition to
establish exact identity `(∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreValue (n : ℕ) (x : ℝ) : ℝ := (shifted n).eval x
/--
Defines `legendreFlux` of type `Polynomial ℝ` by `(X-X^2)*((shifted n).derivative*shifted
j-shifted n*(shifted j).derivative)`.

Use: `chebyshev2.SineContinuum.legendreFlux_derivative` rewrites with this definition to
establish the precise assertion is `(legendreFlux n j).derivative= C
((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted n*shifted j`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendreFlux (n j : ℕ) : Polynomial ℝ :=
  (X-X^2)*((shifted n).derivative*shifted j-shifted n*(shifted j).derivative)

/--
The precise assertion is `((X-X^2)*(p.derivative*q-p*q.derivative)).derivative=
((X-X^2)*p.derivative).derivative*q-p*((X-X^2)*q.derivative).derivative`.

Use: `chebyshev2.SineContinuum.legendreFlux_derivative` rewrites with this identity to
establish the precise assertion is `(legendreFlux n j).derivative= C
((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted n*shifted j`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem polynomial_green_identity (p q : Polynomial ℝ) :
    ((X-X^2)*(p.derivative*q-p*q.derivative)).derivative=
      ((X-X^2)*p.derivative).derivative*q-p*((X-X^2)*q.derivative).derivative := by
  simp only [derivative_mul,derivative_sub]
  ring

/--
The precise assertion is `(legendreFlux n j).derivative= C ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted
n*shifted j`.

Use: `chebyshev2.SineContinuum.legendre_orthogonal` rewrites with this identity to
establish exact identity `(∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.shifted_sturm`,
`chebyshev2.SineContinuum.polynomial_green_identity` with the arguments shown in the proof.
-/
theorem legendreFlux_derivative (n j : ℕ) :
    (legendreFlux n j).derivative=
      C ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*shifted n*shifted j := by
  have hn := eq_neg_of_add_eq_zero_left (shifted_sturm n)
  have hj := eq_neg_of_add_eq_zero_left (shifted_sturm j)
  rw [legendreFlux,polynomial_green_identity,hn,hj,map_sub]
  ring

/--
The stated quantitative bound `StrictMono (fun n : ℕ => (n:ℝ)*(n+1))`.

Use: `chebyshev2.SineContinuum.legendre_orthogonal` uses this identity to establish exact
identity `(∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem shifted_eigenvalue_strictMono : StrictMono (fun n : ℕ => (n:ℝ)*(n+1)) := by
  intro n j hnj
  have h : (n:ℝ) < j := by exact_mod_cast hnj
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/--
Orthogonality of the actual community Legendre polynomials, obtained from their Sturm equation
and a boundary flux that vanishes at both ends.

Exact identity `(∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0`.

Use: `chebyshev2.SineContinuum.legendre_cross_bonnet` uses this identity to establish exact
identity `((n:ℝ)+1)*legendreNorm n=(2*(n:ℝ)+3)*legendreCross n`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem legendre_orthogonal {n j : ℕ} (hnj : n ≠ j) :
    (∫ x in (0:ℝ)..1, legendreValue n x*legendreValue j x)=0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let P := legendreFlux n j
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => P.hasDerivAt x)
    (P.derivative.continuous.intervalIntegrable (μ := volume) 0 1)
  have h0 : P.eval 0=0 := by simp [P,legendreFlux]
  have h1 : P.eval 1=0 := by simp [P,legendreFlux]
  rw [h0,h1,sub_self] at hi
  have he : (fun x => P.derivative.eval x)=
      (fun x => ((j:ℝ)*(j+1)-(n:ℝ)*(n+1))*(legendreValue n x*legendreValue j x)) := by
    funext x
    rw [show P=legendreFlux n j from rfl,legendreFlux_derivative]
    simp only [eval_mul,eval_C,legendreValue]
    ring
  rw [he,intervalIntegral.integral_const_mul] at hi
  have hc : (j:ℝ)*(j+1)-(n:ℝ)*(n+1) ≠ 0 := by
    intro hz
    exact hnj (shifted_eigenvalue_strictMono.injective (sub_eq_zero.mp hz).symm)
  exact (mul_eq_zero.mp hi).resolve_left hc

/--
Defines `legendre₁` of type `ℝ` by `(-1/2)*(shifted n).derivative.eval ((1-z)/2)`.

Use: `chebyshev2.SineContinuum.legendre_derivative` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (legendre n) (legendre₁ n z) z`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendre₁ (n : ℕ) (z : ℝ) : ℝ := (-1/2)*(shifted n).derivative.eval ((1-z)/2)
/--
Defines `legendre₂` of type `ℝ` by `(1/4)*(shifted n).derivative.derivative.eval ((1-z)/2)`.

Use: `chebyshev2.SineContinuum.legendre_ode` uses this definition to establish exact
identity `(1-z^2)*legendre₂ n z-2*z*legendre₁ n z+(n:ℝ)*(n+1)*legendre n z=0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def legendre₂ (n : ℕ) (z : ℝ) : ℝ := (1/4)*(shifted n).derivative.derivative.eval ((1-z)/2)

/--
The actual derivative at the stated point: `HasDerivAt (legendre n) (legendre₁ n z) z`.

Use: `chebyshev2.SineContinuum.regularLeftFlux_continuousAt_zero` uses this derivative
formula to establish continuity at the stated point: `ContinuousAt (regularLeftFlux n) 0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem legendre_derivative (n : ℕ) (z : ℝ) : HasDerivAt (legendre n) (legendre₁ n z) z := by
  have hc := ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).div_const 2
  have hd := ((shifted n).hasDerivAt ((1-z)/2)).comp z hc
  convert hd using 1
  · funext x; rfl
  · dsimp [legendre₁]; ring

/--
The actual derivative at the stated point: `HasDerivAt (legendre₁ n) (legendre₂ n z) z`.

Use: `chebyshev2.SineContinuum.regularLeftFlux_continuousAt_zero` uses this derivative
formula to establish continuity at the stated point: `ContinuousAt (regularLeftFlux n) 0`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem legendre₁_derivative (n : ℕ) (z : ℝ) : HasDerivAt (legendre₁ n) (legendre₂ n z) z := by
  have hc := ((hasDerivAt_const z (1:ℝ)).sub (hasDerivAt_id z)).div_const 2
  have hd := (((shifted n).derivative.hasDerivAt ((1-z)/2)).comp z hc).const_mul (-1/2:ℝ)
  convert hd using 1
  · funext x; rfl
  · dsimp [legendre₂]; ring

/--
Exact identity `(1-z^2)*legendre₂ n z-2*z*legendre₁ n z+(n:ℝ)*(n+1)*legendre n z=0`.

Use: `chebyshev2.SineContinuum.upsilon_explicit_ode` uses this identity to establish exact
identity `-upsilon₂ n t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.shifted_ode` with the
arguments shown in the proof.
-/
theorem legendre_ode (n : ℕ) (z : ℝ) :
    (1-z^2)*legendre₂ n z-2*z*legendre₁ n z+(n:ℝ)*(n+1)*legendre n z=0 := by
  have h := shifted_ode n ((1-z)/2)
  dsimp [legendre,legendre₁,legendre₂]
  linear_combination h

end
end chebyshev2.SineContinuum

import chebyshev2.SineContinuum.LegendreOrthogonality
import chebyshev2.SineContinuum.Profiles

/-!
Article: chebyshev2, Proposition 2.
The genuine second derivative solves Lemma 5's singular equation with the exact printed eigenvalue.
Use: `chebyshev2.SineContinuum.upsilon_explicit_ode` feeds
`chebyshev2.SineContinuum.upsilon_ode` (upsilon ode).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Lemma 5's literal normalized sine--Legendre functions.

Use: `chebyshev2.SineContinuum.upsilon_ode` uses this definition to establish exact
identity `-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def upsilon (n : ℕ) (t : ℝ) : ℝ :=
  √(π*((n:ℝ)+1/2))*chebyshev1.SineJacobi.profileWeight t*legendre n (cos (π*t))
/--
Defines `mu` of type `ℝ` by `π^2*((n:ℝ)+1/2)^2`.

Use: `chebyshev2.SineContinuum.upsilon_ode` uses this definition to establish exact
identity `-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.green_mercer_uniform`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def mu (n : ℕ) : ℝ := π^2*((n:ℝ)+1/2)^2

/--
Defines `upsilon₁` of type `ℝ` by `√(π*((n:ℝ)+1/2))* (chebyshev1.SineJacobi.profileWeight₁
t*legendre n (cos (π*t))+ chebyshev1.SineJacobi.profileWeight t*legendre₁ n (cos
(π*t))*(-π*sin (π*t)))`.

Use: `chebyshev2.SineContinuum.upsilon_derivative` uses this definition to establish the
actual derivative at the stated point: `HasDerivAt (upsilon n) (upsilon₁ n t) t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def upsilon₁ (n : ℕ) (t : ℝ) : ℝ := √(π*((n:ℝ)+1/2))*
  (chebyshev1.SineJacobi.profileWeight₁ t*legendre n (cos (π*t))+
    chebyshev1.SineJacobi.profileWeight t*legendre₁ n (cos (π*t))*(-π*sin (π*t)))
/--
Defines `upsilon₂` of type `ℝ` by `√(π*((n:ℝ)+1/2))* (chebyshev1.SineJacobi.profileWeight₂
t*legendre n (cos (π*t))+ 2*chebyshev1.SineJacobi.profileWeight₁ t*legendre₁ n (cos
(π*t))*(-π*sin (π*t))+ chebyshev1.SineJacobi.profileWeight t*(legendre₂ n (cos
(π*t))*(-π*sin (π*t))^2+ legendre₁ n (cos (π*t))*(-π^2*cos (π*t))))`.

Use: `chebyshev2.SineContinuum.upsilon_explicit_ode` uses this definition to establish
exact identity `-upsilon₂ n t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.
-/
def upsilon₂ (n : ℕ) (t : ℝ) : ℝ := √(π*((n:ℝ)+1/2))*
  (chebyshev1.SineJacobi.profileWeight₂ t*legendre n (cos (π*t))+
    2*chebyshev1.SineJacobi.profileWeight₁ t*legendre₁ n (cos (π*t))*(-π*sin (π*t))+
    chebyshev1.SineJacobi.profileWeight t*(legendre₂ n (cos (π*t))*(-π*sin (π*t))^2+
      legendre₁ n (cos (π*t))*(-π^2*cos (π*t))))

/--
The actual derivative at the stated point: `HasDerivAt (upsilon n) (upsilon₁ n t) t`.

Use: `chebyshev2.SineContinuum.upsilon_ode` uses this derivative formula to establish exact
identity `-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem upsilon_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (upsilon n) (upsilon₁ n t) t := by
  have hz := ((hasDerivAt_id t).const_mul π).cos
  have hp := (legendre_derivative n (cos (π*t))).comp t hz
  have hd := ((chebyshev1.SineJacobi.profileWeight_deriv ht).mul hp).const_mul (√(π*((n:ℝ)+1/2)))
  convert hd using 1
  · funext x; dsimp [upsilon,Function.comp_def]; ring
  · dsimp [upsilon₁]; ring

/--
The actual derivative at the stated point: `HasDerivAt (upsilon₁ n) (upsilon₂ n t) t`.

Use: `chebyshev2.SineContinuum.upsilon_ode` rewrites with this derivative formula to
establish exact identity `-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n
t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem upsilon₁_derivative (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (upsilon₁ n) (upsilon₂ n t) t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hz := ((hasDerivAt_id t).const_mul π).cos
  have hp := (legendre_derivative n (cos (π*t))).comp t hz
  have hp₁ := (legendre₁_derivative n (cos (π*t))).comp t hz
  have hz₁ := (((hasDerivAt_id t).const_mul π).sin).const_mul (-π)
  have hd := (((chebyshev1.SineJacobi.profileWeight₁_deriv ht).mul hp).add
    (((chebyshev1.SineJacobi.profileWeight_deriv ht).mul hp₁).mul hz₁)).const_mul
      (√(π*((n:ℝ)+1/2)))
  convert hd using 1
  · funext x; dsimp [upsilon₁,Function.comp_def]
  · dsimp [upsilon₂]; ring

/--
Exact identity `-((-p^2*s/(2*w)-p^2*z^2/(4*w^3))*f+
2*(p*z/(2*w))*f₁*(-p*s)+w*(f₂*(-p*s)^2+f₁*(-p^2*z)))-
p^2/(4*s^2)*(w*f)=p^2*w*((1/4)*f+2*z*f₁-(1-z^2)*f₂)`.

Use: `chebyshev2.SineContinuum.upsilon_explicit_ode` uses this identity to establish exact
identity `-upsilon₂ n t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
private theorem weight_transform (p s z w f f₁ f₂ : ℝ) (hw : w ≠ 0)
    (hws : w^2=s) (htrig : s^2+z^2=1) :
    -((-p^2*s/(2*w)-p^2*z^2/(4*w^3))*f+
      2*(p*z/(2*w))*f₁*(-p*s)+w*(f₂*(-p*s)^2+f₁*(-p^2*z)))-
      p^2/(4*s^2)*(w*f)=p^2*w*((1/4)*f+2*z*f₁-(1-z^2)*f₂) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hz : z^2=1-s^2 := by linarith
  rw [hz,← hws]
  field_simp [hw]
  ring

/--
The genuine second derivative solves Lemma 5's singular equation with the exact printed
eigenvalue.

Exact identity `-upsilon₂ n t-potential t*upsilon n t=mu n*upsilon n t`.

Use: `chebyshev2.SineContinuum.upsilon_ode` uses this identity to establish the identity
`-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
`_private.chebyshev2.SineContinuum.LegendreEigenfunctions.0.chebyshev2.SineContinuum.weight_transform`,
`chebyshev2.SineContinuum.legendre_ode` with the arguments shown in the proof.
-/
theorem upsilon_explicit_ode (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    -upsilon₂ n t-potential t*upsilon n t=mu n*upsilon n t := by
  -- Use the identities/estimates `chebyshev1.SineJacobi.profileWeight_pos`,
  -- `_private.chebyshev2.SineContinuum.LegendreEigenfunctions.0.chebyshev2.SineContinuum.weight_transform`,
  -- `chebyshev2.SineContinuum.legendre_ode` with the arguments shown in the proof.
  have hw := (chebyshev1.SineJacobi.profileWeight_pos ht).ne'
  have hws : chebyshev1.SineJacobi.profileWeight t^2=sin (π*t) :=
    sq_sqrt (sqrt_pos.mp (chebyshev1.SineJacobi.profileWeight_pos ht)).le
  have ha := weight_transform π (sin (π*t)) (cos (π*t))
    (chebyshev1.SineJacobi.profileWeight t) (legendre n (cos (π*t)))
    (legendre₁ n (cos (π*t))) (legendre₂ n (cos (π*t)))
    hw hws (sin_sq_add_cos_sq _)
  have he := legendre_ode n (cos (π*t))
  dsimp [upsilon₂,upsilon,potential,mu,chebyshev1.SineJacobi.profileWeight₁,
    chebyshev1.SineJacobi.profileWeight₂]
  linear_combination √(π*((n:ℝ)+1/2))*ha-
    √(π*((n:ℝ)+1/2))*π^2*chebyshev1.SineJacobi.profileWeight t*he

/--
Exact identity `-deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Proposition 2.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem upsilon_ode (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    -deriv (deriv (upsilon n)) t-potential t*upsilon n t=mu n*upsilon n t := by
  have he : deriv (upsilon n)=ᶠ[𝓝 t] upsilon₁ n := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact (upsilon_derivative n hx).deriv
  rw [((upsilon₁_derivative n ht).congr_of_eventuallyEq he).deriv]
  exact upsilon_explicit_ode n ht

end
end chebyshev2.SineContinuum

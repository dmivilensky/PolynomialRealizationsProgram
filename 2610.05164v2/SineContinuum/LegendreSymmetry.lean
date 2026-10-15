import «2610.05164v2».SineContinuum.LegendreEigenfunctions

/-!
Article: 2610.05164v2, Proposition 2.
Legendre Symmetry.
Use: `«2610.05164v2».SineContinuum.upsilon₁_reflect` feeds
`«2610.05164v2».SineContinuum.rightFlux_reflect` (right Flux reflect).
Proof chain: `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue` — 2610.05164v2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Polynomial Real
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(shifted n).eval (1-x)=(-1:ℝ)^n*(shifted n).eval x`.

Use: `«2610.05164v2».SineContinuum.legendre_neg` uses this identity to establish the identity
`legendre n (-z)=(-1:ℝ)^n*legendre n z`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem shifted_reflect (n : ℕ) (x : ℝ) :
    (shifted n).eval (1-x)=(-1:ℝ)^n*(shifted n).eval x := by
  have h := Polynomial.shiftedLegendre_eval_symm n (1-x)
  have he (y : ℝ) : aeval y (shiftedLegendre n)=(shifted n).eval y := by
    simp only [shifted,eval_map,aeval_def]
    rfl
  rw [he,he,show (1:ℝ)-(1-x)=x by ring] at h
  exact h

/--
Exact identity `legendre n (-z)=(-1:ℝ)^n*legendre n z`.

Use: `«2610.05164v2».SineContinuum.upsilon_reflect` rewrites with this identity to establish
exact identity `upsilon n (1-t)=(-1:ℝ)^n*upsilon n t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.shifted_reflect` with the
arguments shown in the proof.
-/
theorem legendre_neg (n : ℕ) (z : ℝ) : legendre n (-z)=(-1:ℝ)^n*legendre n z := by
  have h := shifted_reflect n ((1-z)/2)
  simpa only [legendre,show (1:ℝ)-(1-z)/2=(1-(-z))/2 by ring] using h

/--
Exact identity `upsilon n (1-t)=(-1:ℝ)^n*upsilon n t`.

Use: `«2610.05164v2».SineContinuum.upsilon₁_reflect` uses this identity to establish exact
identity `upsilon₁ n (1-t)=-(-1:ℝ)^n*upsilon₁ n t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.legendre_neg` with the
arguments shown in the proof.
-/
theorem upsilon_reflect (n : ℕ) (t : ℝ) : upsilon n (1-t)=(-1:ℝ)^n*upsilon n t := by
  have hs : sin (π*(1-t))=sin (π*t) := by rw [mul_sub,mul_one,sin_pi_sub]
  have hc : cos (π*(1-t))=-cos (π*t) := by rw [mul_sub,mul_one,cos_pi_sub]
  dsimp [upsilon,«2606.16671v2».SineJacobi.profileWeight]
  rw [hs,hc,legendre_neg]
  ring

/--
Exact identity `upsilon₁ n (1-t)=-(-1:ℝ)^n*upsilon₁ n t`.

Use: `«2610.05164v2».SineContinuum.rightFlux_reflect` rewrites with this identity to establish
exact identity `rightFlux n t=-(-1:ℝ)^n*leftFlux n (1-t)`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Source: NIST Digital Library of Mathematical Functions, Chapter 18 — Legendre orthogonality,
Rodrigues formula and Sturm–Liouville equation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem upsilon₁_reflect (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    upsilon₁ n (1-t)=-(-1:ℝ)^n*upsilon₁ n t := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hd := (upsilon_derivative n (reflect_mem ht)).comp t
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))
  have he := (upsilon_derivative n ht).const_mul ((-1:ℝ)^n)
  have hf : (fun x => upsilon n (1-x))=(fun x => (-1:ℝ)^n*upsilon n x) := funext (upsilon_reflect n)
  simp only [Function.comp_def] at hd
  rw [hf] at hd
  have h := hd.unique he
  linarith

end
end «2610.05164v2».SineContinuum

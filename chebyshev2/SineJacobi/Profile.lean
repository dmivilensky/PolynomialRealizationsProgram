import chebyshev2.SineJacobi.Density

/-!
Article: chebyshev2, Theorem 1.1.
The exact formula printed in Theorem 2.5, with its parameter convention.
Result: `chebyshev2.SineJacobi.energy_eq_integral` supplies the stated article conclusion.
-/
namespace chebyshev2.SineJacobi
noncomputable section
open Real Set MeasureTheory

/--
The complete elliptic integral in the parameter convention of chebyshev2.

Use: `chebyshev2.SineJacobi.ellipticK_parameter` rewrites with this definition to establish
exact identity `ellipticK s = chebyshev1.SineJacobi.ellipticK (sqrt s)`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.phi_formula`.
-/
def ellipticK (s : ℝ) : ℝ := ∫ θ in (0:ℝ)..(π/2), 1/sqrt (1-s*sin θ^2)

/--
Exact identity `ellipticK s = chebyshev1.SineJacobi.ellipticK (sqrt s)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 1.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ellipticK_parameter (s : ℝ) (hs : 0 ≤ s) :
    ellipticK s = chebyshev1.SineJacobi.ellipticK (sqrt s) := by simp only [ellipticK, chebyshev1.SineJacobi.ellipticK, sq_sqrt hs]

/--
Exact identity `ellipticK (k^2) = chebyshev1.SineJacobi.ellipticK k`.

Use: `chebyshev2.SineJacobi.phi_formula` rewrites with this identity to establish exact
identity `phi t = 4/π^2*sin (π*t)*ellipticK (sin (π*t/2)^2)*ellipticK (cos (π*t/2)^2)`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.phi_formula`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem ellipticK_square (k : ℝ) : ellipticK (k^2) = chebyshev1.SineJacobi.ellipticK k := by simp only [ellipticK, chebyshev1.SineJacobi.ellipticK]

/--
The exact formula printed in Theorem 2.5, with its parameter convention.

Exact identity `phi t = 4/π^2*sin (π*t)*ellipticK (sin (π*t/2)^2)*ellipticK (cos (π*t/2)^2)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.5.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem phi_formula {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    phi t = 4/π^2*sin (π*t)*ellipticK (sin (π*t/2)^2)*ellipticK (cos (π*t/2)^2) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hs : 0 ≤ sin (π*t) := (sin_pos_of_mem_Ioo
    ⟨mul_pos pi_pos ht.1, by nlinarith [pi_pos,ht.2]⟩).le
  have hsin : sin (π*(1-t)) = sin (π*t) := by
    rw [show π*(1-t) = π-π*t by ring, sin_pi_sub]
  have hhalf : sin (π*(1-t)/2) = cos (π*t/2) := by
    rw [show π*(1-t)/2 = π/2-π*t/2 by ring, sin_pi_div_two_sub]
  simp only [phi, chebyshev1.SineJacobi.sineDensity, chebyshev1.SineJacobi.profileProduct,
    chebyshev1.SineJacobi.sineProfile, hsin, hhalf, ellipticK_square]
  have hp := sq_sqrt pi_pos.le
  have hh := sq_sqrt hs
  field_simp [pi_pos.ne', (sqrt_pos.mpr pi_pos).ne']
  linear_combination 4 * chebyshev1.SineJacobi.ellipticK (sin (π*t/2)) *
    chebyshev1.SineJacobi.ellipticK (cos (π*t/2)) * (π*hh - sin (π*t)*hp)

/--
The stated quantitative bound `0 < phi t`.

Use: `_private.chebyshev2.SineContinuum.Density.0.chebyshev2.SineContinuum.integrand_n`
rewrites with this bound to establish the identity `(SineJacobi.phi t)⁻¹*n (X t)=1`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sqrt_mass`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_pos` with the
arguments shown in the proof.
-/
theorem phi_pos {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 < phi t :=
  mul_pos pi_pos (mul_pos (chebyshev1.SineJacobi.sineProfile_pos ht)
    (chebyshev1.SineJacobi.sineProfile_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩))

/--
Exact identity `(∫ t in (0:ℝ)..1, phi t) = 1`.

Use: `chebyshev2.SineContinuum.green_diagonal_integral` rewrites with this identity to
establish exact identity `(∫ t in (0:ℝ)..1, green t t)=1/2`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.mass`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineDensity_integral` with the
arguments shown in the proof.
-/
theorem phi_integral : (∫ t in (0:ℝ)..1, phi t) = 1 := chebyshev1.SineJacobi.sineDensity_integral
/--
Exact identity `energy = ∫ t in (0:ℝ)..1, phi t^2`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 2.5.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem energy_eq_integral : energy = ∫ t in (0:ℝ)..1, phi t^2 := rfl

end
end chebyshev2.SineJacobi

import chebyshev2.Primal.Speed
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
Article: chebyshev2, Theorem 5.2.
Family.
Result: `chebyshev2.Primal.profile_formula` supplies the stated article conclusion.
-/
namespace chebyshev2.Primal
noncomputable section
open Polynomial Set MeasureTheory
set_option autoImplicit false

/--
Defines `chebyshevDirection` of type `ℝ[X]` by `(Polynomial.Chebyshev.T ℝ (j:ℤ)).comp (2*X-1)`.

Use: `chebyshev2.Primal.centralPolynomial` uses this definition in the displayed
construction of `centralPolynomial`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.profile_difference_bound`.
-/
def chebyshevDirection (j : Nat) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (j:ℤ)).comp (2*X-1)

/--
Defines `centralPolynomial` of type `ℝ[X]` by `∑ j : Fin 17,C (c j)*chebyshevDirection j.val`.

Use: `chebyshev2.Primal.familyPolynomial` uses this definition in the displayed
construction of `familyPolynomial`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.profile_difference_bound`.
-/
def centralPolynomial (c : Fin 17 → ℝ) : ℝ[X] :=
  ∑ j : Fin 17,C (c j)*chebyshevDirection j.val

/--
Defines `familyPolynomial` of type `ℝ[X]` by `centralPolynomial c+∑ i : Fin 6,C (a
i)*chebyshevDirection (directions i)`.

Use: `chebyshev2.Primal.profile` uses this definition in the displayed construction of
`profile`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.profile_formula`.
-/
def familyPolynomial (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    (a : Fin 6 → ℝ) : ℝ[X] :=
  centralPolynomial c+∑ i : Fin 6,C (a i)*chebyshevDirection (directions i)

/--
Defines `profile` of type `ℝ → ℝ` by `(familyPolynomial c directions a).eval`.

Use: `chebyshev2.Primal.familySpeed` uses this definition in the displayed construction of
`familySpeed`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.profile_formula`.
-/
def profile (c : Fin 17 → ℝ) (directions : Fin 6 → Nat) (a : Fin 6 → ℝ) : ℝ → ℝ :=
  (familyPolynomial c directions a).eval

/--
Continuity of the displayed function: `Continuous (profile c directions a)`.

Use: `chebyshev2.Primal.familySpeed` uses this continuity result in the displayed
construction of `familySpeed`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.family_energy_ceiling`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem profile_continuous (c : Fin 17 → ℝ) (directions : Fin 6 → Nat) (a : Fin 6 → ℝ) :
    Continuous (profile c directions a) := Polynomial.continuous _

/--
Defines `familySpeed` of type `chebyshev2.PrescribedSpeed.SpeedData` by `speedData (profile
c directions a) (profile_continuous c directions a)`.

Use: `chebyshev2.Primal.family_ground_exact` uses this definition to establish exact
identity `chebyshev2.GroundState.groundParameter ((familySpeed c directions
a).density_integrable hκ) ((familySpeed c directions a).density_nonneg hκ)=κ`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.family_ground_exact`.
-/
def familySpeed (c : Fin 17 → ℝ) (directions : Fin 6 → Nat) (a : Fin 6 → ℝ) :
    chebyshev2.PrescribedSpeed.SpeedData :=
  speedData (profile c directions a) (profile_continuous c directions a)

/--
Exact identity `chebyshev2.GroundState.groundParameter ((familySpeed c directions
a).density_integrable hκ) ((familySpeed c directions a).density_nonneg hκ)=κ`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 5.2.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` with the arguments shown in
the proof.
-/
theorem family_ground_exact (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    (a : Fin 6 → ℝ) {κ : ℝ} (hκ : 0<κ) :
    chebyshev2.GroundState.groundParameter ((familySpeed c directions a).density_integrable hκ)
      ((familySpeed c directions a).density_nonneg hκ)=κ :=
  (familySpeed c directions a).groundParameter_density hκ

/--
Exact identity `(familySpeed c directions a).D (t^3)=t^2*Real.exp (profile c directions a t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 5.2.

Proof: Use the identities/estimates `chebyshev2.Primal.speed_cubic` with the arguments
shown in the proof.
-/
theorem family_speed_cubic (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    (a : Fin 6 → ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (familySpeed c directions a).D (t^3)=t^2*Real.exp (profile c directions a t) :=
  speed_cubic _ ht

/--
The precise assertion is `profile c directions a t= (∑ j : Fin 17,c j*(Polynomial.Chebyshev.T ℝ
(j.val:ℤ)).eval (2*t-1))+ ∑ i : Fin 6,a i*(Polynomial.Chebyshev.T ℝ (directions i:ℤ)).eval
(2*t-1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Theorem 5.2.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem profile_formula (c : Fin 17 → ℝ) (directions : Fin 6 → Nat)
    (a : Fin 6 → ℝ) (t : ℝ) :
    profile c directions a t=
      (∑ j : Fin 17,c j*(Polynomial.Chebyshev.T ℝ (j.val:ℤ)).eval (2*t-1))+
      ∑ i : Fin 6,a i*(Polynomial.Chebyshev.T ℝ (directions i:ℤ)).eval (2*t-1) := by simp [profile,familyPolynomial,centralPolynomial,chebyshevDirection,eval_finsetSum]

end
end chebyshev2.Primal

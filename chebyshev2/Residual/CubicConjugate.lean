import chebyshev2.Calibration.Tangent

/-!
Article: chebyshev2, Lemma 15.
Lemma 15: the literal maximum of the cubic amplitude defect.
Use: `chebyshev2.Residual.psi_convex` feeds `chebyshev2.DualCertificate.criterion_convex`
(criterion convex).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Residual
noncomputable section
open Set chebyshev2.Calibration

/--
Defines `conjugate` of type `ℝ` by `-y*ν^2-ν^3/2+4/27*(max (y+3*ν/2) 0)^3`.

Use: `chebyshev2.Residual.conjugate_attained` uses this definition to establish exact
identity `y*((maximizer ν y)^2-ν^2)-rho (maximizer ν y) ν=conjugate ν y`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.
-/
def conjugate (ν y : ℝ) : ℝ := -y*ν^2-ν^3/2+4/27*(max (y+3*ν/2) 0)^3
/--
Defines `maximizer` of type `ℝ` by `2*max (y+3*ν/2) 0/3`.

Use: `chebyshev2.Residual.conjugate_attained` uses this definition to establish exact
identity `y*((maximizer ν y)^2-ν^2)-rho (maximizer ν y) ν=conjugate ν y`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.
-/
def maximizer (ν y : ℝ) : ℝ := 2*max (y+3*ν/2) 0/3
/--
Defines `psi` of type `ℝ` by `-x-1/2+4/27*(max (x+3/2) 0)^3`.

Use: `chebyshev2.Residual.conjugate_scale` rewrites with this definition to establish exact
identity `conjugate ν y=ν^3*psi (y/ν)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def psi (x : ℝ) : ℝ := -x-1/2+4/27*(max (x+3/2) 0)^3

/--
The stated quantitative bound `0 ≤ maximizer ν y`.

Use: `chebyshev2.Residual.conjugate_isGreatest` uses this bound to establish the stated
quantitative bound `IsGreatest ((fun n => y*(n^2-ν^2)-rho n ν) '' Ici 0) (conjugate ν y)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem maximizer_nonneg (ν y : ℝ) : 0 ≤ maximizer ν y := by unfold maximizer; positivity

/--
Exact identity `y*((maximizer ν y)^2-ν^2)-rho (maximizer ν y) ν=conjugate ν y`.

Use: `chebyshev2.Residual.conjugate_isGreatest` uses this identity to establish the stated
quantitative bound `IsGreatest ((fun n => y*(n^2-ν^2)-rho n ν) '' Ici 0) (conjugate ν y)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem conjugate_attained (ν y : ℝ) :
    y*((maximizer ν y)^2-ν^2)-rho (maximizer ν y) ν=conjugate ν y := by
  unfold maximizer conjugate rho
  rcases le_total (y+3*ν/2) 0 with h | h
  · rw [max_eq_right h]
    ring
  · rw [max_eq_left h]
    ring

/--
The stated quantitative bound `y*(n^2-ν^2)-rho n ν ≤ conjugate ν y`.

Use: `chebyshev2.Residual.conjugate_convex` uses this bound to establish the precise
assertion is `ConvexOn ℝ univ (conjugate ν)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem le_conjugate {n : ℝ} (hn : 0 ≤ n) (ν y : ℝ) :
    y*(n^2-ν^2)-rho n ν ≤ conjugate ν y := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  unfold conjugate rho
  rcases le_total (y+3*ν/2) 0 with h | h
  · rw [max_eq_right h]
    have hp := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg n)
    have hc : 0 ≤ n^3 := by positivity
    nlinarith
  · rw [max_eq_left h]
    have hp := mul_nonneg (sq_nonneg (n-2*(y+3*ν/2)/3))
      (show 0 ≤ n+(y+3*ν/2)/3 by positivity)
    nlinarith

/--
The formula is an attained maximum, not a definition of a supremum.

The stated quantitative bound `IsGreatest ((fun n => y*(n^2-ν^2)-rho n ν) '' Ici 0) (conjugate
ν y)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 15.

Proof: Use the identities/estimates `chebyshev2.Residual.maximizer_nonneg`,
`chebyshev2.Residual.conjugate_attained`, `chebyshev2.Residual.le_conjugate` with the
arguments shown in the proof.
-/
theorem conjugate_isGreatest (ν y : ℝ) :
    IsGreatest ((fun n => y*(n^2-ν^2)-rho n ν) '' Ici 0) (conjugate ν y) := by
  refine ⟨⟨maximizer ν y,maximizer_nonneg ν y,conjugate_attained ν y⟩,?_⟩
  rintro z ⟨n,hn,rfl⟩
  exact le_conjugate hn ν y

/--
Equivalence of the displayed criteria: `conjugate ν y ≤ z ↔ ∀ n : ℝ, 0 ≤ n → y*(n^2-ν^2)-rho n
ν ≤ z`.

Use: `chebyshev2.Residual.conjugate_convex` rewrites with this bound to establish the
precise assertion is `ConvexOn ℝ univ (conjugate ν)`.

Article: chebyshev2, Theorem 3.5 via `chebyshev2.Residual.pointwise_criterion`.

Proof: Use the identities/estimates `chebyshev2.Residual.le_conjugate`,
`chebyshev2.Residual.conjugate_attained`, `chebyshev2.Residual.maximizer_nonneg` with
the arguments shown in the proof.
-/
theorem conjugate_le_iff (ν y z : ℝ) :
    conjugate ν y ≤ z ↔ ∀ n : ℝ, 0 ≤ n → y*(n^2-ν^2)-rho n ν ≤ z := by
  constructor
  · exact fun h n hn => (le_conjugate hn ν y).trans h
  · intro h
    rw [← conjugate_attained]
    exact h _ (maximizer_nonneg ν y)

/--
Exact identity `conjugate ν y=ν^3*psi (y/ν)`.

Use: `chebyshev2.DualCertificate.normalized_state_criterion` rewrites with this identity to
establish equivalence of the displayed criteria: `conjugate ν (a-(-τ*Q/d+ν*e)-bΨ)≤ criterionRhs
κ ν Q (-τ*Q/d+ν*e) τ bΨ dΨ ↔ criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem conjugate_scale {ν : ℝ} (hν : 0 < ν) (y : ℝ) :
    conjugate ν y=ν^3*psi (y/ν) := by
  have hm : max (y+3*ν/2) 0=ν*max (y/ν+3/2) 0 := by
    rw [mul_max_of_nonneg _ _ hν.le,mul_zero]
    congr 1
    field_simp
  rw [conjugate,psi,hm]
  field_simp

/--
Exact identity `psi x=2/3*x^2+4/27*x^3`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev2, Lemma 15.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem psi_polynomial {x : ℝ} (hx : -(3/2:ℝ) ≤ x) :
    psi x=2/3*x^2+4/27*x^3 := by
  rw [psi,max_eq_left (by linarith)]
  ring

/--
Convexity follows directly from the proved maximum of affine functions.

The precise assertion is `ConvexOn ℝ univ (conjugate ν)`.

Use: `chebyshev2.Residual.psi_convex` uses this assertion to establish the precise
assertion is `ConvexOn ℝ univ psi`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Residual.conjugate_le_iff`,
`chebyshev2.Residual.le_conjugate` with the arguments shown in the proof.
-/
theorem conjugate_convex (ν : ℝ) : ConvexOn ℝ univ (conjugate ν) := by
  -- Use the identities/estimates `chebyshev2.Residual.conjugate_le_iff`,
  -- `chebyshev2.Residual.le_conjugate` with the arguments shown in the proof.
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  rw [conjugate_le_iff]
  intro n hn
  have hx := mul_le_mul_of_nonneg_left (le_conjugate hn ν x) ha
  have hy := mul_le_mul_of_nonneg_left (le_conjugate hn ν y) hb
  simp only [smul_eq_mul] at *
  calc
    (a*x+b*y)*(n^2-ν^2)-rho n ν =
        a*(x*(n^2-ν^2)-rho n ν)+b*(y*(n^2-ν^2)-rho n ν) := by
          linear_combination rho n ν*hab
    _ ≤ a*conjugate ν x+b*conjugate ν y := add_le_add hx hy

/--
The precise assertion is `ConvexOn ℝ univ psi`.

Use: `chebyshev2.DualCertificate.criterion_convex` uses this assertion to establish the
stated quantitative bound `ConvexOn ℝ univ (fun θ : ℝ => criterion (b₀+b₁*θ) (c₀+c₁*θ) e l)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem psi_convex : ConvexOn ℝ univ psi := by
  have he : conjugate 1=psi := by funext x; simp [conjugate,psi]
  rw [← he]
  exact conjugate_convex 1

end
end chebyshev2.Residual

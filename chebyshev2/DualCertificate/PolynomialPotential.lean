import chebyshev2.Residual.StatePotential
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
Article: chebyshev2, Theorem 3.6.
Definition 7(ii): the literal rational polynomial potential and the endpoint cancellations used in
Lemma 16(iv).
Use: `chebyshev2.DualCertificate.PolynomialPotential.raw_dPotential_endpoints` feeds
`chebyshev2.DualCertificate.PolynomialPotential.centered_d_endpoints` (centered d endpoints).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open chebyshev2.Residual chebyshev2.Calibration
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/--
Six rational polynomials determining the state potential. Their placement in the
linear/quadratic state terms is fixed by inner; the outer factor (2-q)² enforces the required
right-endpoint normalization.

Use: `chebyshev2.DualCertificate.PolynomialPotential.inner` uses this record of data and
proof obligations in the displayed construction of `inner`. Its inputs and component formulas
are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
structure PolynomialPotential where
  /-- Polynomial coefficient of the h component, evaluated at the q coordinate. -/
  Ph : Polynomial ℚ
  /-- Polynomial coefficient of q*u₀ in the inner potential. -/
  P₀ : Polynomial ℚ
  /-- Polynomial coefficient of q*u₁ in the inner potential. -/
  P₁ : Polynomial ℚ
  /-- Polynomial coefficient of u₀² in the inner potential. -/
  P₀₀ : Polynomial ℚ
  /-- Polynomial coefficient of u₀*u₁ in the inner potential. -/
  P₀₁ : Polynomial ℚ
  /-- Polynomial coefficient of u₁² in the inner potential. -/
  P₁₁ : Polynomial ℚ

namespace PolynomialPotential
variable (P : PolynomialPotential)

/--
Defines `inner` of type `ℝ` by `P.Ph.aeval Y.1*Y.2.2.2+Y.1*P.P₀.aeval Y.1*Y.2.1+ Y.1*P.P₁.aeval
Y.1*Y.2.2.1+P.P₀₀.aeval Y.1*Y.2.1^2+ P.P₀₁.aeval Y.1*Y.2.1*Y.2.2.1+P.P₁₁.aeval Y.1*Y.2.2.1^2`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.inner_smooth` uses this definition to
establish smoothness to the stated order: `ContDiff ℝ ∞ P.inner`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def inner (Y : State) : ℝ :=
  P.Ph.aeval Y.1*Y.2.2.2+Y.1*P.P₀.aeval Y.1*Y.2.1+
    Y.1*P.P₁.aeval Y.1*Y.2.2.1+P.P₀₀.aeval Y.1*Y.2.1^2+
    P.P₀₁.aeval Y.1*Y.2.1*Y.2.2.1+P.P₁₁.aeval Y.1*Y.2.2.1^2

/--
Defines `raw` of type `ℝ` by `(2-Y.1)^2*P.inner Y`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.raw_left` rewrites with this
definition to establish the identity `P.raw (0,0,0,0)=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def raw (Y : State) : ℝ := (2-Y.1)^2*P.inner Y

/--
Smoothness to the stated order: `ContDiff ℝ ∞ P.inner`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.raw_right_fderiv` uses this assertion
to establish the identity `fderiv ℝ P.raw (2,u₀,u₁,h)=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem inner_smooth : ContDiff ℝ ∞ P.inner := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hp (p : Polynomial ℚ) : ContDiff ℝ ∞ (fun Y : State => p.aeval Y.1) :=
    (p.contDiff_aeval ∞).comp contDiff_fst
  unfold inner
  exact ((((((hp P.Ph).mul (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))).add
    ((contDiff_fst.mul (hp P.P₀)).mul (contDiff_fst.comp contDiff_snd))).add
    ((contDiff_fst.mul (hp P.P₁)).mul (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))).add
    ((hp P.P₀₀).mul ((contDiff_fst.comp contDiff_snd).pow 2))).add
    (((hp P.P₀₁).mul (contDiff_fst.comp contDiff_snd)).mul
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd)))).add
    ((hp P.P₁₁).mul ((contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).pow 2))

/--
Smoothness to the stated order: `ContDiff ℝ ∞ P.raw`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centeredB_identity` rewrites with this
assertion to establish `P.centeredB N side hκ t U₀ U₁ θ= -bPotential κ
(P.centered N hκ) (unnormalize κ (side.q t,U₀,U₁,θ))/(t*N.root κ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.PolynomialPotential.inner_smooth` with the arguments shown in
the proof.
-/
theorem raw_smooth : ContDiff ℝ ∞ P.raw :=
  ((contDiff_const.sub contDiff_fst).pow 2).mul P.inner_smooth

/--
Exact identity `P.raw (0,0,0,0)=0`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centered_boundary` rewrites with this
identity to establish the identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem raw_left : P.raw (0,0,0,0)=0 := by simp [raw,inner]

/--
Exact identity `P.raw (2,u₀,u₁,h)=0`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centered_boundary` rewrites with this
identity to establish the identity `P.centered N hκ (0,0,0,0)=P.centered N hκ (2,0,0,2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem raw_right (u₀ u₁ h : ℝ) : P.raw (2,u₀,u₁,h)=0 := by simp [raw]

/--
Exact identity `fderiv ℝ P.raw (2,u₀,u₁,h)=0`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.raw_dPotential_endpoints` rewrites
with this identity to establish the identity `dPotential P.raw Y=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem raw_right_fderiv (u₀ u₁ h : ℝ) :
    fderiv ℝ P.raw (2,u₀,u₁,h)=0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hf : HasFDerivAt (fun Y : State => (2-Y.1)^2)
      (0 : State →L[ℝ] ℝ) (2,u₀,u₁,h) := by
    convert ((hasFDerivAt_const (𝕜 := ℝ) (2:ℝ) (2,u₀,u₁,h)).sub hasFDerivAt_fst).pow 2 using 1
    simp
  have hi := (P.inner_smooth.differentiable (by norm_num) (2,u₀,u₁,h)).hasFDerivAt
  have hd := (hf.mul hi).fderiv
  rw [show P.raw=(fun Y : State => (2-Y.1)^2)*P.inner by funext Y; rfl]
  simpa using hd

/--
Exact identity `dPotential P.raw Y=0`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centered_d_endpoints` rewrites with
this identity to establish the identity `dPotential (P.centered N hκ) Y=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.DualCertificate.PolynomialPotential.raw_right_fderiv` with the arguments shown
in the proof.
-/
theorem raw_dPotential_endpoints {Y : State} (hq : Y.1=0 ∧ Y.2.1=0 ∧
    Y.2.2.1=0 ∧ Y.2.2.2=0 ∨ Y.1=2) : dPotential P.raw Y=0 := by
  -- Use the identities/estimates
  -- `chebyshev2.DualCertificate.PolynomialPotential.raw_right_fderiv` with the arguments
  -- shown in the proof.
  rcases hq with ⟨hq,h₀,h₁,hh⟩ | hq
  · have he : Y=(0,0,0,0) := by ext <;> assumption
    rw [he,dPotential]
    have hz : driftVector (0,0,0,0)=0 := by ext <;> norm_num [driftVector,Q]
    rw [hz,map_zero]
  · obtain ⟨q,u₀,u₁,h⟩ := Y
    dsimp only at hq
    subst q
    rw [dPotential,P.raw_right_fderiv]
    rfl

end PolynomialPotential
end
end chebyshev2.DualCertificate

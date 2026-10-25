import chebyshev2.Residual.StatePotential
import chebyshev2.Residual.Pointwise
import chebyshev2.Residual.Price

/-!
Article: chebyshev2, Lemma 16.
Theorem 3.5's gauge transformation of the actual C1 potential.
Use: `chebyshev2.Residual.gaugePotential_d` feeds `chebyshev2.Residual.criterion_gauge`
(criterion gauge).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_analytic` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Residual
noncomputable section
open chebyshev2.Calibration
set_option backward.isDefEq.respectTransparency false

/--
Defines `gaugePotential` of type `State → ℝ` by `fun Y => Ψ Y-F Y.1`.

Use: `chebyshev2.Residual.gaugePotential_boundary` rewrites with this definition to
establish exact identity `gaugePotential Ψ F (0,0,0,0)=gaugePotential Ψ F (2,0,0,2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def gaugePotential (Ψ : State → ℝ) (F : ℝ → ℝ) : State → ℝ := fun Y => Ψ Y-F Y.1

/--
Smoothness to the stated order: `ContDiff ℝ 1 (gaugePotential Ψ F)`.

Use: `chebyshev2.DualCertificate.PolynomialPotential.centered_c1` uses this assertion to
establish smoothness to the stated order: `ContDiff ℝ 1 (P.centered N hκ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem gaugePotential_c1 {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (gaugePotential Ψ F) :=
  hΨ.sub (hF.comp contDiff_fst)

/--
Exact identity `fderiv ℝ (gaugePotential Ψ F) Y V=fderiv ℝ Ψ Y V-deriv F Y.1*V.1`.

Use: `chebyshev2.Residual.gaugePotential_b` rewrites with this identity to establish exact
identity `bPotential κ (gaugePotential Ψ F) Y=bPotential κ Ψ Y-κ*deriv F Y.1`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gaugePotential_fderiv {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hF : ContDiff ℝ 1 F) (Y V : State) :
    fderiv ℝ (gaugePotential Ψ F) Y V=fderiv ℝ Ψ Y V-deriv F Y.1*V.1 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hf := ((hF.differentiable (by norm_num) Y.1).hasDerivAt.hasFDerivAt).comp Y hasFDerivAt_fst
  have he := ((hΨ.differentiable (by norm_num) Y).hasFDerivAt.sub hf).fderiv
  change fderiv ℝ (gaugePotential Ψ F) Y=_ at he
  rw [he]
  simp only [sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  change fderiv ℝ Ψ Y V-V.1*deriv F Y.1=fderiv ℝ Ψ Y V-deriv F Y.1*V.1
  ring

/--
Exact identity `bPotential κ (gaugePotential Ψ F) Y=bPotential κ Ψ Y-κ*deriv F Y.1`.

Use: `chebyshev2.Residual.criterion_gauge` rewrites with this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Residual.gaugePotential_fderiv` with the
arguments shown in the proof.
-/
theorem gaugePotential_b {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hF : ContDiff ℝ 1 F) (κ : ℝ) (Y : State) :
    bPotential κ (gaugePotential Ψ F) Y=bPotential κ Ψ Y-κ*deriv F Y.1 := by
  unfold bPotential
  rw [gaugePotential_fderiv hΨ hF]
  simp only [inputVector]
  ring

/--
Exact identity `dPotential (gaugePotential Ψ F) Y=dPotential Ψ Y-Q Y.1*deriv F Y.1`.

Use: `chebyshev2.Residual.criterion_gauge` rewrites with this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Residual.gaugePotential_fderiv` with the
arguments shown in the proof.
-/
theorem gaugePotential_d {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hF : ContDiff ℝ 1 F) (Y : State) :
    dPotential (gaugePotential Ψ F) Y=dPotential Ψ Y-Q Y.1*deriv F Y.1 := by
  unfold dPotential
  rw [gaugePotential_fderiv hΨ hF]
  simp only [driftVector]
  ring

/--
Exact identity `gaugePotential Ψ F (0,0,0,0)=gaugePotential Ψ F (2,0,0,2)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem gaugePotential_boundary {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : Ψ (0,0,0,0)=Ψ (2,0,0,2)) (hF : F 0=F 2) :
    gaugePotential Ψ F (0,0,0,0)=gaugePotential Ψ F (2,0,0,2) := by simp only [gaugePotential,hΨ,hF]

/--
The precise assertion is `conjugate ν (a-(η+κ*deriv F Y.1)-bPotential κ (gaugePotential Ψ F)
Y)= conjugate ν (a-η-bPotential κ Ψ Y) ∧ criterionRhs κ ν (Q Y.1) (η+κ*deriv F Y.1) τ
(bPotential κ (gaugePotential Ψ F) Y) (dPotential (gaugePotential Ψ F) Y)= criterionRhs κ ν (Q
Y.1) η τ (bPotential κ Ψ Y) (dPotential Ψ Y)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 16.

Proof: Use the identities/estimates `chebyshev2.Residual.gaugePotential_b`,
`chebyshev2.Residual.gaugePotential_d`, `chebyshev2.Residual.gauge_argument` with the
arguments shown in the proof.
-/
theorem criterion_gauge {Ψ : State → ℝ} {F : ℝ → ℝ}
    (hΨ : ContDiff ℝ 1 Ψ) (hF : ContDiff ℝ 1 F) {κ : ℝ} (hκ : κ ≠ 0)
    (ν a η τ : ℝ) (Y : State) :
    conjugate ν (a-(η+κ*deriv F Y.1)-bPotential κ (gaugePotential Ψ F) Y)=
      conjugate ν (a-η-bPotential κ Ψ Y) ∧
    criterionRhs κ ν (Q Y.1) (η+κ*deriv F Y.1) τ
        (bPotential κ (gaugePotential Ψ F) Y) (dPotential (gaugePotential Ψ F) Y)=
      criterionRhs κ ν (Q Y.1) η τ (bPotential κ Ψ Y) (dPotential Ψ Y) := by
  -- Use the identities/estimates `chebyshev2.Residual.gaugePotential_b`,
  -- `chebyshev2.Residual.gaugePotential_d`, `chebyshev2.Residual.gauge_argument` with
  -- the arguments shown in the proof.
  rw [gaugePotential_b hΨ hF,gaugePotential_d hΨ hF,gauge_argument,gauge_rhs hκ]
  exact ⟨rfl,rfl⟩

end
end chebyshev2.Residual

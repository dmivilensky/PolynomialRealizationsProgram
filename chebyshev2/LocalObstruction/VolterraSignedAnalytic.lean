import chebyshev2.LocalObstruction.VolterraSignedInverse
import chebyshev2.LocalObstruction.VolterraAnalytic

/-!
Article: chebyshev2, Lemma 26.
Entire real analyticity of signed finite-dimensional Jost families.
Use: `chebyshev2.LocalObstruction.volterraSolution_signed_joint_analytic` feeds
`chebyshev2.LocalObstruction.perturbTransmission_signed_analytic` (perturb Transmission signed
analytic).
Proof chain: `chebyshev2.LocalObstruction.groundObservationWitness` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open MeasureTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Supplies the typeclass structure specified by `IsBoundedSMul ℝ (VolterraSpace →L[ℝ]
VolterraSpace)`. This lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
local instance : IsBoundedSMul ℝ (VolterraSpace →L[ℝ] VolterraSpace) := by
  convert! (IsBoundedSMul.of_norm_smul_le (fun (r : ℝ) (f : VolterraSpace →L[ℝ] VolterraSpace) =>
    ContinuousLinearMap.opNorm_smul_le r f)) using 1

/--
Supplies the typeclass `IsScalarTower ℝ (VolterraSpace →L[ℝ] VolterraSpace) (VolterraSpace
→L[ℝ] VolterraSpace)` by the displayed field definitions/proofs. Each proof field establishes
the corresponding class law.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
local instance : IsScalarTower ℝ (VolterraSpace →L[ℝ] VolterraSpace) (VolterraSpace →L[ℝ] VolterraSpace) where
  smul_assoc r A B := by
    apply ContinuousLinearMap.ext
    intro f
    change (r • A) (B f)=r • (A (B f))
    rfl

 /--
The precise assertion is `AnalyticAt ℝ (volterraSolution hm hv) p`.

Use: `chebyshev2.LocalObstruction.perturbTransmission_signed_analytic` uses this assertion
to establish `AnalyticAt ℝ (perturbTransmission hm hv) p`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.perturb_integrable`,
`chebyshev2.LocalObstruction.volterra_signedPencil_unit`,
`chebyshev2.LocalObstruction.volterraPencil_joint_analytic` with the arguments shown in the
proof.
-/
theorem volterraSolution_signed_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) :
    AnalyticAt ℝ (volterraSolution hm hv) p := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.perturb_integrable`,
  -- `chebyshev2.LocalObstruction.volterra_signedPencil_unit`,
  -- `chebyshev2.LocalObstruction.volterraPencil_joint_analytic` with the arguments shown
  -- in the proof.
  let P := fun z : (ι → ℝ) × ℝ => volterraPencil (perturb_integrable hm hv z.1) z.2
  have hu : IsUnit (P p) := volterra_signedPencil_unit (perturb_integrable hm hv p.1) p.2
  have hi : AnalyticAt ℝ Ring.inverse (P p) := by
    simpa only [IsUnit.unit_spec] using
      (analyticAt_inverse (𝕜 := ℝ) (A := VolterraSpace →L[ℝ] VolterraSpace) hu.unit)
  have hp := hi.comp (f := P) (volterraPencil_joint_analytic hm hv p)
  exact ((ContinuousLinearMap.apply ℝ VolterraSpace (1:VolterraSpace)).analyticAt _).comp
    (f := fun z => Ring.inverse (P z)) hp

end
end chebyshev2.LocalObstruction

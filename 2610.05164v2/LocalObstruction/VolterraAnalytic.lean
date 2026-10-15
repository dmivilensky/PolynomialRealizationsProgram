import «2610.05164v2».LocalObstruction.VolterraInverse
import «2610.05164v2».LocalObstruction.VolterraPerturbation
import «2610.05164v2».LocalObstruction.VolterraFunctionals
import «2610.05164v2».HalfLine.BoundaryResolvent
import Mathlib.Analysis.Analytic.Constructions

/-!
Article: 2610.05164v2, Theorem 6.1.
Analyticity of the actual Jost solution under finite signed L1 density perturbations, using a fixed
Banach-space inverse.
Use: `«2610.05164v2».LocalObstruction.volterraSolution_joint_analytic` feeds
`«2610.05164v2».LocalObstruction.perturbTransmission_joint_analytic` (perturb Transmission joint
analytic).
Proof chain: `«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` — 2610.05164v2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open MeasureTheory Real «2610.05164v2».Filters «2610.05164v2».HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Supplies the typeclass structure specified by `IsBoundedSMul ℝ (VolterraSpace →L[ℝ]
VolterraSpace)`. This lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: 2610.05164v2, Theorem 6.1.

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

Article: 2610.05164v2, Theorem 6.1.

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
Defines `volterraSolution` of type `VolterraSpace` by `Ring.inverse (volterraPencil
(perturb_integrable hm hv p.1) p.2) 1`.

Use: `«2610.05164v2».LocalObstruction.volterraSolution_actual` uses this definition to
establish exact identity `volterraSolution hm hv p=jostBCF (perturb_integrable hm hv p.1) hn
hs`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraSolution {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) : VolterraSpace :=
  Ring.inverse (volterraPencil (perturb_integrable hm hv p.1) p.2) 1

 /--
Exact identity `volterraSolution hm hv p=jostBCF (perturb_integrable hm hv p.1) hn hs`.

Use: `«2610.05164v2».LocalObstruction.perturbTransmission_actual` rewrites with this identity
to establish the identity `perturbTransmission hm hv p=transmission p.2 (perturb m v p.1)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.perturb_integrable`,
`«2610.05164v2».LocalObstruction.volterraPencil_unit`,
`«2610.05164v2».LocalObstruction.volterraScaled_apply` with the arguments shown in the proof.
-/
theorem volterraSolution_actual {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ)
    (hn : ∀ x,0≤perturb m v p.1 x) (hs : 0≤p.2) :
    volterraSolution hm hv p=jostBCF (perturb_integrable hm hv p.1) hn hs := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.perturb_integrable`,
  -- `«2610.05164v2».LocalObstruction.volterraPencil_unit`,
  -- `«2610.05164v2».LocalObstruction.volterraScaled_apply` with the arguments shown in the
  -- proof.
  let hi := perturb_integrable hm hv p.1
  have hu := volterraPencil_unit hi hn hs
  have he : volterraPencil hi p.2 (jostBCF hi hn hs)=1 := by
    apply BoundedContinuousFunction.ext
    intro x
    change jost p.2 (perturb m v p.1) x-(p.2 • volterraMap hi) (jostBCF hi hn hs) x=1
    rw [volterraScaled_apply]
    change jost p.2 (perturb m v p.1) x-volterra p.2 (perturb m v p.1) (jost p.2 (perturb m v p.1)) x=1
    linarith [jost_equation hi hn hs x]
  unfold volterraSolution
  change Ring.inverse (ContinuousLinearMap.id ℝ VolterraSpace-p.2 • volterraMap hi) 1=_
  rw [Ring.inverse_of_isUnit hu]
  exact inverseOfUnit_apply_of_eq _ _ he

 /--
The precise assertion is `AnalyticAt ℝ (volterraSolution hm hv) ((0:ι → ℝ),s)`.

Use: `«2610.05164v2».LocalObstruction.perturbTransmission_joint_analytic` uses this assertion
to establish `AnalyticAt ℝ (perturbTransmission hm hv) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.perturb_integrable`,
`«2610.05164v2».LocalObstruction.volterraPencil_unit`,
`«2610.05164v2».LocalObstruction.volterraPencil_joint_analytic` with the arguments shown in the
proof.
-/
theorem volterraSolution_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hn : ∀ x,0≤m x) (hv : ∀ i,Integrable (v i)) {s : ℝ} (hs : 0≤s) :
    AnalyticAt ℝ (volterraSolution hm hv) ((0:ι → ℝ),s) := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.perturb_integrable`,
  -- `«2610.05164v2».LocalObstruction.volterraPencil_unit`,
  -- `«2610.05164v2».LocalObstruction.volterraPencil_joint_analytic` with the arguments shown
  -- in the proof.
  let P := fun z : (ι → ℝ) × ℝ => volterraPencil (perturb_integrable hm hv z.1) z.2
  have hu : IsUnit (P ((0:ι → ℝ),s)) :=
    volterraPencil_unit (perturb_integrable hm hv 0) (fun x => by simpa [perturb] using hn x) hs
  have hi : AnalyticAt ℝ Ring.inverse (P ((0:ι → ℝ),s)) := by
    simpa only [IsUnit.unit_spec] using (analyticAt_inverse (𝕜 := ℝ) (A := VolterraSpace →L[ℝ] VolterraSpace) hu.unit)
  have hp := hi.comp (f := P) (volterraPencil_joint_analytic hm hv ((0:ι → ℝ),s))
  exact ((ContinuousLinearMap.apply ℝ VolterraSpace (1:VolterraSpace)).analyticAt _).comp
    (f := fun z => Ring.inverse (P z)) hp

end
end «2610.05164v2».LocalObstruction

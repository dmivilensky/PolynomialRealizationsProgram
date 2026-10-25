import chebyshev2.LocalObstruction.VolterraSignedInverse
import chebyshev2.LocalObstruction.VolterraAnalytic
import chebyshev2.LocalObstruction.InverseVariation

/-!
Article: chebyshev2, Theorem 6.1.
The signed Jost solution is the actual inverse of the causal pencil.
Use: `chebyshev2.LocalObstruction.signedJost_density_derivative` feeds
`chebyshev2.LocalObstruction.signedTransmission_density_derivative` (signed Transmission density
derivative).
Proof chain: `chebyshev2.LocalObstruction.groundObservationWitness` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real chebyshev2.Filters chebyshev2.HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

 /--
Defines `signedJost` of type `VolterraSpace` by `Ring.inverse (volterraPencil hm s) 1`.

Use: `chebyshev2.LocalObstruction.signedJostVariation` uses this definition in the
displayed construction of `signedJostVariation`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def signedJost {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) : VolterraSpace :=
  Ring.inverse (volterraPencil hm s) 1

 /--
Exact identity `volterraPencil hm s (signedJost hm s)=1`.

Use: `chebyshev2.LocalObstruction.signedJost_equation` uses this identity to establish
exact identity `signedJost hm s x=1+volterra s m (signedJost hm s) x`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.volterra_signedPencil_unit`,
`chebyshev2.HalfLine.inverseOfUnit_right` with the arguments shown in the proof.
-/
theorem signedJost_pencil {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) :
    volterraPencil hm s (signedJost hm s)=1 := by
  have hu : IsUnit (volterraPencil hm s) := volterra_signedPencil_unit hm s
  unfold signedJost
  rw [Ring.inverse_of_isUnit hu]
  exact DFunLike.congr_fun (inverseOfUnit_right _ hu) 1

 /--
Exact identity `signedJost hm s x=1+volterra s m (signedJost hm s) x`.

Use: `chebyshev2.LocalObstruction.signedJost_actual` uses this identity to establish exact
identity `signedJost hm s=jostBCF hm hn hs`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.signedJost_pencil`,
`chebyshev2.LocalObstruction.volterraScaled_apply` with the arguments shown in the proof.
-/
theorem signedJost_equation {m : ℝ → ℝ} (hm : Integrable m) (s x : ℝ) :
    signedJost hm s x=1+volterra s m (signedJost hm s) x := by
  have he := congrArg (fun f : VolterraSpace => f x) (signedJost_pencil hm s)
  change signedJost hm s x-(s • volterraMap hm) (signedJost hm s) x=1 at he
  rw [volterraScaled_apply] at he
  linarith

 /--
Exact identity `signedJost hm s=jostBCF hm hn hs`.

Use: `chebyshev2.LocalObstruction.signedTransmission_actual` rewrites with this identity to
establish exact identity `signedTransmission hm s=transmission s m`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `chebyshev2.Filters.jost_unique_of_bounded_measurable`,
`chebyshev2.LocalObstruction.signedJost_equation` with the arguments shown in the proof.
-/
theorem signedJost_actual {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) : signedJost hm s=jostBCF hm hn hs := by
  have he := jost_unique_of_bounded_measurable hm hn hs
    (signedJost hm s).continuous.aestronglyMeasurable (signedJost hm s).norm_coe_le_norm
    (signedJost_equation hm s)
  apply BoundedContinuousFunction.ext
  intro x
  exact congrFun he x

 /--
Exact identity `volterraMap (hm.add (hv.smul ε))=volterraMap hm+ε • volterraMap hv`.

Use: `chebyshev2.LocalObstruction.signedJost_density_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
signedJost (hm.add (hv.smul ε)) s) (signedJostVariation hm hv s) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem volterraMap_affine {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (ε : ℝ) :
    volterraMap (hm.add (hv.smul ε))=volterraMap hm+ε • volterraMap hv := by
  have he := volterraMap_perturb hm (fun _ : Unit => hv) (fun _ => ε)
  have hz : perturb m (fun _ : Unit => v) (fun _ => ε)=m+ε • v := by
    funext x
    simp [perturb]
  simpa only [hz,Finset.univ_unique,Finset.sum_singleton] using he

 /--
Defines `signedJostVariation` of type `VolterraSpace` by `Ring.inverse (volterraPencil hm s)
((s • volterraMap hv) (signedJost hm s))`.

Use: `chebyshev2.LocalObstruction.signedJostVariation_equation` uses this definition to
establish exact identity `signedJostVariation hm hv s x=volterra s m (signedJostVariation hm hv
s) x+ volterra s v (signedJost hm s) x`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def signedJostVariation {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (s : ℝ) : VolterraSpace :=
  Ring.inverse (volterraPencil hm s) ((s • volterraMap hv) (signedJost hm s))

 /--
Exact identity `signedJostVariation hm hv s x=volterra s m (signedJostVariation hm hv s) x+
volterra s v (signedJost hm s) x`.

Use: `chebyshev2.LocalObstruction.signedJostVariation_mass` uses this identity to establish
the precise assertion is `(∫ x,v x*signedJost hm s x)+(∫ x,m x*signedJostVariation hm hv s x)=
∫ x,v x*signedJost hm s x*signedJost hm s (-x)`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.volterra_signedPencil_unit`,
`chebyshev2.HalfLine.inverseOfUnit_right`,
`chebyshev2.LocalObstruction.volterraScaled_apply` with the arguments shown in the proof.
-/
theorem signedJostVariation_equation {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (s x : ℝ) :
    signedJostVariation hm hv s x=volterra s m (signedJostVariation hm hv s) x+
      volterra s v (signedJost hm s) x := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.volterra_signedPencil_unit`,
  -- `chebyshev2.HalfLine.inverseOfUnit_right`,
  -- `chebyshev2.LocalObstruction.volterraScaled_apply` with the arguments shown in the
  -- proof.
  have hu : IsUnit (volterraPencil hm s) := volterra_signedPencil_unit hm s
  have he : volterraPencil hm s (signedJostVariation hm hv s)=(s • volterraMap hv) (signedJost hm s) := by
    unfold signedJostVariation
    rw [Ring.inverse_of_isUnit hu]
    exact DFunLike.congr_fun (inverseOfUnit_right _ hu) _
  have he' := congrArg (fun f : VolterraSpace => f x) he
  change signedJostVariation hm hv s x-(s • volterraMap hm) (signedJostVariation hm hv s) x=
    (s • volterraMap hv) (signedJost hm s) x at he'
  rw [volterraScaled_apply,volterraScaled_apply] at he'
  linarith

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => signedJost (hm.add
(hv.smul ε)) s) (signedJostVariation hm hv s) 0`.

Use: `chebyshev2.LocalObstruction.signedTransmission_density_derivative` uses this
derivative formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε :
ℝ => signedTransmission (hm.add (hv.smul ε)) s) (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s
(-x))) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem signedJost_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (s : ℝ) :
    HasDerivAt (fun ε : ℝ => signedJost (hm.add (hv.smul ε)) s) (signedJostVariation hm hv s) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun ε : ℝ => volterraPencil (hm.add (hv.smul ε)) s)=
      fun ε : ℝ => volterraPencil hm s+ε • (-(s • volterraMap hv)) := by
    funext ε
    simp only [volterraPencil,volterraMap_affine hm hv ε]
    module
  have hu : IsUnit (volterraPencil hm s) := volterra_signedPencil_unit hm s
  have hd := inverse_affine_derivative (volterraPencil hm s) (-(s • volterraMap hv)) hu (1:VolterraSpace)
  simp_rw [← congrFun he] at hd
  convert! hd using 1
  simp only [signedJostVariation,signedJost,neg_apply,map_neg,neg_neg]

end
end chebyshev2.LocalObstruction

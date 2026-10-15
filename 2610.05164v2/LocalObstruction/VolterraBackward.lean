import «2610.05164v2».LocalObstruction.VolterraSignedSolution
import «2610.05164v2».LocalObstruction.VolterraAdjoint

/-!
Article: 2610.05164v2, Theorem 6.1.
Reflection supplies the actual adjoint Jost solution for even densities.
Use: `«2610.05164v2».LocalObstruction.signedJostVariation_mass` feeds
`«2610.05164v2».LocalObstruction.signedTransmission_density_derivative` (signed Transmission density
derivative).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Filters «2610.05164v2».HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Defines `reflectBCF` of type `VolterraSpace` by `f.compContinuous ⟨fun x =>
-x,continuous_neg⟩`.

Use: `«2610.05164v2».LocalObstruction.signedJostVariation_mass` uses this definition to
establish the precise assertion is `(∫ x,v x*signedJost hm s x)+(∫ x,m x*signedJostVariation hm
hv s x)= ∫ x,v x*signedJost hm s x*signedJost hm s (-x)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def reflectBCF (f : VolterraSpace) : VolterraSpace :=
  f.compContinuous ⟨fun x => -x,continuous_neg⟩

 /--
Exact identity `reflectBCF f x=f (-x)`.

Use: `«2610.05164v2».LocalObstruction.signedJost_backward` rewrites with this identity to
establish the precise assertion is `reflectBCF (signedJost hm s) y= 1+s/2*(∫ x,volterraKernel x
y*(m x*reflectBCF (signedJost hm s) x))`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem reflectBCF_apply (f : VolterraSpace) (x : ℝ) : reflectBCF f x=f (-x) := rfl

 /--
The precise assertion is `reflectBCF (signedJost hm s) y= 1+s/2*(∫ x,volterraKernel x y*(m
x*reflectBCF (signedJost hm s) x))`.

Use: `«2610.05164v2».LocalObstruction.signedJostVariation_mass` uses this identity to establish
the precise assertion is `(∫ x,v x*signedJost hm s x)+(∫ x,m x*signedJostVariation hm hv s x)=
∫ x,v x*signedJost hm s x*signedJost hm s (-x)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem signedJost_backward {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ)
    (he : ∀ x,m (-x)=m x) (y : ℝ) :
    reflectBCF (signedJost hm s) y=
      1+s/2*(∫ x,volterraKernel x y*(m x*reflectBCF (signedJost hm s) x)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hj := bounded_forcing_integrable hm (signedJost hm s).continuous.aestronglyMeasurable
    (signedJost hm s).norm_coe_le_norm
  have h := signedJost_equation hm s (-y)
  rw [volterra_full_integral hj] at h
  change signedJost hm s (-y)=_ at h
  have hi : (∫ z,volterraKernel (-y) z*(m z*signedJost hm s z))=
      ∫ x,volterraKernel x y*(m x*reflectBCF (signedJost hm s) x) := by
    rw [← integral_neg_eq_self (fun x => volterraKernel x y*(m x*reflectBCF (signedJost hm s) x)) volume]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [reflectBCF_apply,neg_neg,he]
      have hk : volterraKernel (-y) z=volterraKernel (-z) y := by
        simpa using (volterraKernel_reflect (-y) z).symm
      rw [hk])
  rw [hi] at h
  exact h

 /--
The precise assertion is `(∫ x,v x*signedJost hm s x)+(∫ x,m x*signedJostVariation hm hv s x)=
∫ x,v x*signedJost hm s x*signedJost hm s (-x)`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_density_derivative` uses this identity
to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
signedTransmission (hm.add (hv.smul ε)) s) (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s
(-x))) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.volterra_variation_mass`,
`«2610.05164v2».LocalObstruction.signedJost_backward`,
`«2610.05164v2».LocalObstruction.signedJostVariation_equation` with the arguments shown in the
proof.
-/
theorem signedJostVariation_mass {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (s : ℝ) (he : ∀ x,m (-x)=m x) :
    (∫ x,v x*signedJost hm s x)+(∫ x,m x*signedJostVariation hm hv s x)=
      ∫ x,v x*signedJost hm s x*signedJost hm s (-x) :=
  volterra_variation_mass hm hv s (signedJost hm s) (reflectBCF (signedJost hm s))
    (signedJostVariation hm hv s) (signedJost_backward hm s he)
    (signedJostVariation_equation hm hv s)

end
end «2610.05164v2».LocalObstruction

import «2610.05164v2».LocalObstruction.VolterraDuality
import «2610.05164v2».LocalObstruction.VolterraFunctionals
import «2610.05164v2».LocalObstruction.VolterraInverse

/-!
Article: 2610.05164v2, Theorem 6.1.
Adjoint identities for the actual Volterra kernel.
Use: `«2610.05164v2».LocalObstruction.volterra_variation_mass` feeds
`«2610.05164v2».LocalObstruction.signedJostVariation_mass` (signed Jost Variation mass).
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
Exact identity `volterraKernel (-y) (-x)=volterraKernel x y`.

Use: `«2610.05164v2».LocalObstruction.signedJost_backward` uses this identity to establish the
precise assertion is `reflectBCF (signedJost hm s) y= 1+s/2*(∫ x,volterraKernel x y*(m
x*reflectBCF (signedJost hm s) x))`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.volterraKernel_max` with
the arguments shown in the proof.
-/
theorem volterraKernel_reflect (x y : ℝ) : volterraKernel (-y) (-x)=volterraKernel x y := by
  rw [volterraKernel_max,volterraKernel_max]
  congr 3
  ring

 /--
The precise assertion is `(∫ x,m x*R x*p x)-(∫ x,m x*p x)= ∫ x,m x*R x*volterra s m p x`.

Use: `«2610.05164v2».LocalObstruction.volterra_variation_mass` uses this identity to establish
exact identity `(∫ x,v x*L x)+(∫ x,m x*p x)=∫ x,v x*L x*R x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem volterra_adjoint_identity {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ)
    (R p : VolterraSpace)
    (hR : ∀ y,R y=1+s/2*(∫ x,volterraKernel x y*(m x*R x))) :
    (∫ x,m x*R x*p x)-(∫ x,m x*p x)=
      ∫ x,m x*R x*volterra s m p x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have ha := bounded_forcing_integrable hm R.continuous.aestronglyMeasurable R.norm_coe_le_norm
  have hb := bounded_forcing_integrable hm p.continuous.aestronglyMeasurable p.norm_coe_le_norm
  have hab := bounded_forcing_integrable ha p.continuous.aestronglyMeasurable p.norm_coe_le_norm
  have hswap := volterra_pairing_swap ha hb
  calc
    _ = ∫ y,(m y*p y)*(R y-1) := by
      rw [← integral_sub hab hb]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by dsimp only;ring)
    _ = s/2*(∫ y,(m y*p y)*(∫ x,volterraKernel x y*(m x*R x))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by dsimp only;rw [hR];ring)
    _ = s/2*(∫ x,(m x*R x)*(∫ y,volterraKernel x y*(m y*p y))) := by rw [hswap]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        rw [volterra_full_integral hb]
        ring)

 /--
Exact identity `(∫ x,v x*L x)+(∫ x,m x*p x)=∫ x,v x*L x*R x`.

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
theorem volterra_variation_mass {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (s : ℝ) (L R p : VolterraSpace)
    (hR : ∀ y,R y=1+s/2*(∫ x,volterraKernel x y*(m x*R x)))
    (hp : ∀ x,p x=volterra s m p x+volterra s v L x) :
    (∫ x,v x*L x)+(∫ x,m x*p x)=∫ x,v x*L x*R x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have ha := bounded_forcing_integrable hm R.continuous.aestronglyMeasurable R.norm_coe_le_norm
  have hb := bounded_forcing_integrable hv L.continuous.aestronglyMeasurable L.norm_coe_le_norm
  have hmp := bounded_forcing_integrable ha p.continuous.aestronglyMeasurable p.norm_coe_le_norm
  have hmv := bounded_forcing_integrable ha ((s • volterraMap hm) p).continuous.aestronglyMeasurable
    ((s • volterraMap hm) p).norm_coe_le_norm
  have hvv := bounded_forcing_integrable ha ((s • volterraMap hv) L).continuous.aestronglyMeasurable
    ((s • volterraMap hv) L).norm_coe_le_norm
  have hsplit : (∫ x,m x*R x*p x)=
      (∫ x,m x*R x*volterra s m p x)+(∫ x,m x*R x*volterra s v L x) := by
    rw [← integral_add (by simpa only [volterraScaled_apply] using hmv)
      (by simpa only [volterraScaled_apply] using hvv)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only;rw [hp];ring)
  have hid := volterra_adjoint_identity hm s R p hR
  have he : (∫ x,m x*R x*volterra s v L x)=∫ x,v x*L x*(R x-1) := by
    calc
      _ = s/2*(∫ x,(m x*R x)*(∫ y,volterraKernel x y*(v y*L y))) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          dsimp only;rw [volterra_full_integral hb];ring)
      _ = s/2*(∫ y,(v y*L y)*(∫ x,volterraKernel x y*(m x*R x))) := by
        rw [volterra_pairing_swap ha hb]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by dsimp only;rw [hR];ring)
  have hsub : (∫ x,v x*L x*(R x-1))=(∫ x,v x*L x*R x)-(∫ x,v x*L x) := by
    rw [← integral_sub (bounded_forcing_integrable hb R.continuous.aestronglyMeasurable R.norm_coe_le_norm) hb]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only;ring)
  rw [he,hsub] at hsplit
  linarith

end
end «2610.05164v2».LocalObstruction

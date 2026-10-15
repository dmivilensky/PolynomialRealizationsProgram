import «2610.05164v2».LocalObstruction.VolterraBackward
import «2610.05164v2».LocalObstruction.ObservationAnalytic

/-!
Article: 2610.05164v2, Theorem 6.1.
Actual first variations of transmission, valid also at negative scales.
Use: `«2610.05164v2».LocalObstruction.signedTransmission_scale_derivative` feeds
`«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` (ground Coupling finite c1).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Filters «2610.05164v2».HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Defines `signedTransmission` of type `ℝ` by `1+s/2*volterraMass hm (signedJost hm s)`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_actual` rewrites with this definition
to establish the identity `signedTransmission hm s=transmission s m`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def signedTransmission {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) : ℝ :=
  1+s/2*volterraMass hm (signedJost hm s)

 /--
Exact identity `signedTransmission hm s=transmission s m`.

Use: `«2610.05164v2».LocalObstruction.singleH_density_derivative` rewrites with this identity
to establish the actual derivative at the stated point: `HasDerivAt (singleH hm hv s) (s*(∫
x,greenKernel s m x x*v x)) 0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.signedJost_actual` with
the arguments shown in the proof.
-/
theorem signedTransmission_actual {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) : signedTransmission hm s=transmission s m := by
  rw [signedTransmission,signedJost_actual hm hn hs]
  rfl

 /--
Exact identity `volterraMass (hm.add (hv.smul ε)) f=volterraMass hm f+ε*volterraMass hv f`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_density_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
signedTransmission (hm.add (hv.smul ε)) s) (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s
(-x))) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem volterraMass_affine {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (ε : ℝ) (f : VolterraSpace) :
    volterraMass (hm.add (hv.smul ε)) f=volterraMass hm f+ε*volterraMass hv f := by
  have he := volterraMass_perturb hm (fun _ : Unit => hv) (fun _ => ε) f
  have hz : perturb m (fun _ : Unit => v) (fun _ => ε)=m+ε • v := by
    funext x
    simp [perturb]
  simpa only [hz,Finset.univ_unique,Finset.sum_singleton] using he

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => signedTransmission (hm.add
(hv.smul ε)) s) (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s (-x))) 0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
groundCoupling (m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/
(∫ x,m x*(H1.rep G.u x)^2)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem signedTransmission_density_derivative {m v : ℝ → ℝ}
    (hm : Integrable m) (hv : Integrable v) (s : ℝ) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (fun ε : ℝ => signedTransmission (hm.add (hv.smul ε)) s)
      (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s (-x))) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hL := signedJost_density_derivative hm hv s
  have hM := (volterraMass hm).hasFDerivAt.comp_hasDerivAt (0:ℝ) hL
  have hV := (volterraMass hv).hasFDerivAt.comp_hasDerivAt (0:ℝ) hL
  have hd := ((hM.add ((hasDerivAt_id (0:ℝ)).mul hV)).const_mul (s/2)).const_add 1
  have hz : signedJost (hm.add (hv.smul (0:ℝ))) s=signedJost hm s := by
    congr 1
    simp
  dsimp only [Function.comp_def,Pi.add_apply,Pi.mul_apply,id_eq] at hd
  simp only [zero_mul,add_zero,one_mul,hz] at hd
  have hf : (fun ε : ℝ => signedTransmission (hm.add (hv.smul ε)) s)=
      fun ε => 1+s/2*(volterraMass hm (signedJost (hm.add (hv.smul ε)) s)+
        ε*volterraMass hv (signedJost (hm.add (hv.smul ε)) s)) := by
    funext ε
    rw [signedTransmission,volterraMass_affine]
  rw [hf]
  have hmass := signedJostVariation_mass hm hv s he
  rw [add_comm] at hmass
  simpa only [volterraMass_apply,hmass] using hd

 /--
Defines `signedJostScaleVariation` of type `VolterraSpace` by `Ring.inverse (volterraPencil hm
s) (volterraMap hm (signedJost hm s))`.

Use: `«2610.05164v2».LocalObstruction.signedJostVariation_self` rewrites with this definition
to establish the identity `signedJostVariation hm hm s=s • signedJostScaleVariation hm s`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def signedJostScaleVariation {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) : VolterraSpace :=
  Ring.inverse (volterraPencil hm s) (volterraMap hm (signedJost hm s))

 /--
The actual derivative at the stated point: `HasDerivAt (signedJost hm)
(signedJostScaleVariation hm s) s`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_scale_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (signedTransmission
hm) ((1/2:ℝ)*(∫ x,m x*signedJost hm s x*signedJost hm s (-x))) s`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem signedJost_scale_derivative {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) :
    HasDerivAt (signedJost hm) (signedJostScaleVariation hm s) s := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hu : IsUnit (volterraPencil hm s) := volterra_signedPencil_unit hm s
  have hd := inverse_affine_derivative (volterraPencil hm s) (-volterraMap hm) hu (1:VolterraSpace)
  have hf : (fun ε : ℝ => Ring.inverse (volterraPencil hm s+ε • (-volterraMap hm)) 1)=
      fun ε => signedJost hm (s+ε) := by
    funext ε
    congr 2
    unfold volterraPencil
    module
  rw [hf] at hd
  have he : -(Ring.inverse (volterraPencil hm s)) ((-volterraMap hm) ((Ring.inverse (volterraPencil hm s)) 1))=
      signedJostScaleVariation hm s := by
    simp only [neg_apply,map_neg,neg_neg,signedJostScaleVariation,signedJost]
  rw [he] at hd
  have h := hd.scomp_of_eq s ((hasDerivAt_id s).sub_const s) (by simp)
  convert! h using 1 <;> simp only [one_smul,Function.comp_def,add_sub_cancel,id_eq]

 /--
Exact identity `signedJostVariation hm hm s=s • signedJostScaleVariation hm s`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_scale_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt
(signedTransmission hm) ((1/2:ℝ)*(∫ x,m x*signedJost hm s x*signedJost hm s (-x))) s`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem signedJostVariation_self {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) :
    signedJostVariation hm hm s=s • signedJostScaleVariation hm s := by simp only [signedJostVariation,signedJostScaleVariation,smul_apply,map_smul]

 /--
The actual derivative at the stated point: `HasDerivAt (signedTransmission hm) ((1/2:ℝ)*(∫ x,m
x*signedJost hm s x*signedJost hm s (-x))) s`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
groundCoupling (m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/
(∫ x,m x*(H1.rep G.u x)^2)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem signedTransmission_scale_derivative {m : ℝ → ℝ} (hm : Integrable m)
    (s : ℝ) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (signedTransmission hm)
      ((1/2:ℝ)*(∫ x,m x*signedJost hm s x*signedJost hm s (-x))) s := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hL := signedJost_scale_derivative hm s
  have hM := (volterraMass hm).hasFDerivAt.comp_hasDerivAt s hL
  have hd := (((hasDerivAt_id s).div_const 2).mul hM).const_add 1
  have hmass := signedJostVariation_mass hm hm s he
  rw [signedJostVariation_self] at hmass
  change (∫ x,m x*signedJost hm s x)+(∫ x,m x*(s*signedJostScaleVariation hm s x))=_ at hmass
  have hi : (∫ x,m x*(s*signedJostScaleVariation hm s x))=
      s*(∫ x,m x*signedJostScaleVariation hm s x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp only;ring)
  rw [hi] at hmass
  dsimp only [Function.comp_def,Pi.mul_apply,id_eq] at hd
  convert! hd using 1
  simp only [volterraMass_apply]
  linarith

end
end «2610.05164v2».LocalObstruction

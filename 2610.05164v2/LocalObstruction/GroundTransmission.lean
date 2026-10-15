import «2610.05164v2».LocalObstruction.GroundJost
import «2610.05164v2».LocalObstruction.TransmissionVariation

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual ground coupling is a zero of signed transmission, and this zero has a nonzero scale
derivative at every even density with exponential moment.
Use: `«2610.05164v2».LocalObstruction.groundTransmission_scale_positive` feeds
`«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` (ground Coupling finite c1).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Filters «2610.05164v2».HalfLine «2610.05164v2».GroundState «2610.05164v2».Sobolev «2610.05164v2».Continuum
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Exact identity `groundLeftAmplitude G=groundParameter hm hn/2*volterraMass hm (groundLeft G
hM)`.

Use: `«2610.05164v2».LocalObstruction.signedTransmission_at_ground` uses this identity to
establish exact identity `signedTransmission hm (-groundParameter hm hn)=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem groundLeftAmplitude_mass {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    groundLeftAmplitude G=groundParameter hm hn/2*volterraMass hm (groundLeft G hM) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [volterraMass_apply,← integral_const_mul]
  unfold groundLeftAmplitude
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only [groundSource]
    rw [groundLeft_apply]
    ring)

 /--
Exact identity `signedTransmission hm (-groundParameter hm hn)=0`.

Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.groundLeftAmplitude_mass`,
`«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost`,
`«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` with the arguments shown in the
proof.
-/
theorem signedTransmission_at_ground {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    signedTransmission hm (-groundParameter hm hn)=0 := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.groundLeftAmplitude_mass`,
  -- `«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost`,
  -- `«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` with the arguments shown in
  -- the proof.
  have hA := groundLeftAmplitude_mass G hM
  rw [groundLeft_eq_signedJost G hM,map_smul,smul_eq_mul] at hA
  have hz : groundLeftAmplitude G*signedTransmission hm (-groundParameter hm hn)=0 := by
    unfold signedTransmission
    nlinarith [hA]
  exact (mul_eq_zero.mp hz).resolve_left (groundLeftAmplitude_positive G hM).ne'

 /--
The stated quantitative bound `0<signedJost hm (-groundParameter hm hn) x`.

Use: `«2610.05164v2».LocalObstruction.groundTransmission_scale_positive` uses this bound to
establish the stated quantitative bound `0<∫ x,m x*signedJost hm (-groundParameter hm hn)
x*signedJost hm (-groundParameter hm hn) (-x)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.signedJost_at_ground`,
`«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` with the arguments shown in the
proof.
-/
theorem signedJost_ground_positive {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) (x : ℝ) :
    0<signedJost hm (-groundParameter hm hn) x := by
  rw [signedJost_at_ground G hM]
  exact div_pos (mul_pos (exp_pos _) (G.positive x)) (groundLeftAmplitude_positive G hM)

 /--
The stated quantitative bound `0<∫ x,m x*signedJost hm (-groundParameter hm hn) x*signedJost hm
(-groundParameter hm hn) (-x)`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_density_derivative` uses this bound to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling
(m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m
x*(H1.rep G.u x)^2)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem groundTransmission_scale_positive {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    0<∫ x,m x*signedJost hm (-groundParameter hm hn) x*signedJost hm (-groundParameter hm hn) (-x) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let L := signedJost hm (-groundParameter hm hn)
  have hi := bounded_forcing_integrable
    (bounded_forcing_integrable hm L.continuous.aestronglyMeasurable L.norm_coe_le_norm)
    (reflectBCF L).continuous.aestronglyMeasurable (reflectBCF L).norm_coe_le_norm
  have hnonneg : ∀ x,0≤m x*L x*L (-x) := fun x =>
    mul_nonneg (mul_nonneg (hn x) (signedJost_ground_positive G hM x).le)
      (signedJost_ground_positive G hM (-x)).le
  apply lt_of_le_of_ne (integral_nonneg hnonneg)
  intro hz
  have heq := (integral_eq_zero_iff_of_nonneg hnonneg hi).mp hz.symm
  have hmzero : m=ᵐ[volume] 0 := by
    filter_upwards [heq] with x hx
    change m x*L x*L (-x)=0 at hx
    exact ((mul_eq_zero.mp hx).resolve_right (signedJost_ground_positive G hM (-x)).ne' |> mul_eq_zero.mp).resolve_right
      (signedJost_ground_positive G hM x).ne'
  have hm0 : (∫ x,m x)=0 := by rw [integral_congr_ae hmzero];simp
  exact G.mass_positive.ne' hm0

end
end «2610.05164v2».LocalObstruction

import «2610.05164v2».LocalObstruction.GroundVolterraKernel
import «2610.05164v2».LocalObstruction.VolterraSignedSolution

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual positive ground state is the signed Jost solution at -kappa, normalized by its proved
left exponential coefficient.
Use: `«2610.05164v2».LocalObstruction.signedJost_at_ground` feeds
`«2610.05164v2».LocalObstruction.signedJost_ground_positive` (signed Jost ground positive).
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
Defines `groundLeftAmplitude` of type `ℝ` by `∫ y,exp (-y)*groundSource G y`.

Use: `«2610.05164v2».LocalObstruction.groundLeft` uses this definition in the displayed
construction of `groundLeft`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def groundLeftAmplitude {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) : ℝ := ∫ y,exp (-y)*groundSource G y

 /--
The stated quantitative bound `0<groundLeftAmplitude G`.

Use: `«2610.05164v2».LocalObstruction.signedJost_at_ground` uses this bound to establish exact
identity `signedJost hm (-groundParameter hm hn) x=exp (-x)*H1.rep G.u x/groundLeftAmplitude
G`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.ground_left_exponential_bound` with the arguments shown in the
proof.
-/
theorem groundLeftAmplitude_positive {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    0<groundLeftAmplitude G :=
  (mul_pos (exp_pos (-(0:ℝ))) (G.positive 0)).trans_le (ground_left_exponential_bound G hM 0)

 /--
Defines `groundLeft` of type `VolterraSpace` by `BoundedContinuousFunction.ofNormedAddCommGroup
(fun x => exp (-x)*H1.rep G.u x) (continuous_exp.comp continuous_neg |>.mul (H1.continuous_rep
G.u)) (groundLeftAmplitude G) (fun x => by rw [Real.norm_eq_abs,abs_of_pos (mul_pos (exp_pos _)
(G.positive x))] exact ground_left_exponential_bound G hM x)`.

Use: `«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost` uses this definition to
establish exact identity `groundLeft G hM=groundLeftAmplitude G • signedJost hm
(-groundParameter hm hn)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.
-/
def groundLeft {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) : VolterraSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => exp (-x)*H1.rep G.u x)
    (continuous_exp.comp continuous_neg |>.mul (H1.continuous_rep G.u))
    (groundLeftAmplitude G) (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (mul_pos (exp_pos _) (G.positive x))]
      exact ground_left_exponential_bound G hM x)

 /--
Exact identity `groundLeft G hM x=exp (-x)*H1.rep G.u x`.

Use: `«2610.05164v2».LocalObstruction.groundLeft_equation` rewrites with this identity to
establish the precise assertion is `groundLeft G hM x-groundLeftAmplitude G= volterra
(-groundParameter hm hn) m (groundLeft G hM) x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem groundLeft_apply {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) (x : ℝ) :
    groundLeft G hM x=exp (-x)*H1.rep G.u x := rfl

 /--
The precise assertion is `groundLeft G hM x-groundLeftAmplitude G= volterra (-groundParameter
hm hn) m (groundLeft G hM) x`.

Use: `«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost` uses this identity to establish
exact identity `groundLeft G hM=groundLeftAmplitude G • signedJost hm (-groundParameter hm
hn)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem groundLeft_equation {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) (x : ℝ) :
    groundLeft G hM x-groundLeftAmplitude G=
      volterra (-groundParameter hm hn) m (groundLeft G hM) x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hj := groundSource_integrable G
  have hw := groundSource_weighted_integrable G hM
  have hf := bounded_forcing_integrable hm (groundLeft G hM).continuous.aestronglyMeasurable
    (groundLeft G hM).norm_coe_le_norm
  rw [groundLeft_apply,ground_source_rep G x]
  change exp (-x)*H1.rep (convolution (groundSource G)) x-groundLeftAmplitude G=_
  rw [convolution_rep hj,← integral_const_mul,groundLeftAmplitude,
    ← integral_sub ((convolution_kernel_integrable hj x).const_mul _) hw,
    volterra_full_integral hf,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [← mul_assoc,← sub_mul,ground_volterra_kernel,groundLeft_apply]
    dsimp only [groundSource]
    ring)

 /--
Exact identity `groundLeft G hM=groundLeftAmplitude G • signedJost hm (-groundParameter hm
hn)`.

Use: `«2610.05164v2».LocalObstruction.signedJost_at_ground` uses this identity to establish
exact identity `signedJost hm (-groundParameter hm hn) x=exp (-x)*H1.rep G.u
x/groundLeftAmplitude G`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.volterra_signedPencil_unit`,
`«2610.05164v2».LocalObstruction.volterraScaled_apply`,
`«2610.05164v2».LocalObstruction.groundLeft_equation` with the arguments shown in the proof.
-/
theorem groundLeft_eq_signedJost {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) :
    groundLeft G hM=groundLeftAmplitude G • signedJost hm (-groundParameter hm hn) := by
  -- Use the identities/estimates `«2610.05164v2».LocalObstruction.volterra_signedPencil_unit`,
  -- `«2610.05164v2».LocalObstruction.volterraScaled_apply`,
  -- `«2610.05164v2».LocalObstruction.groundLeft_equation` with the arguments shown in the
  -- proof.
  let P := volterraPencil hm (-groundParameter hm hn)
  have hu : IsUnit P := volterra_signedPencil_unit hm _
  have he : P (groundLeft G hM)=groundLeftAmplitude G • (1:VolterraSpace) := by
    apply BoundedContinuousFunction.ext
    intro x
    change groundLeft G hM x-((-groundParameter hm hn) • volterraMap hm) (groundLeft G hM) x=
      groundLeftAmplitude G*1
    rw [volterraScaled_apply]
    linarith [groundLeft_equation G hM x]
  calc
    _ = inverseOfUnit P hu (P (groundLeft G hM)) :=
      (DFunLike.congr_fun (inverseOfUnit_left P hu) _).symm
    _ = groundLeftAmplitude G • inverseOfUnit P hu (1:VolterraSpace) := by rw [he,map_smul]
    _ = _ := by
      congr 1
      unfold signedJost
      change inverseOfUnit P hu 1=Ring.inverse P 1
      rw [Ring.inverse_of_isUnit hu]
      congr 1

 /--
Exact identity `signedJost hm (-groundParameter hm hn) x=exp (-x)*H1.rep G.u
x/groundLeftAmplitude G`.

Use: `«2610.05164v2».LocalObstruction.groundJost_product` rewrites with this identity to
establish the precise assertion is `signedJost hm (-groundParameter hm hn) x*signedJost hm
(-groundParameter hm hn) (-x)= (H1.rep G.u x)^2/(groundLeftAmplitude G)^2`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.groundLeft_eq_signedJost`,
`«2610.05164v2».LocalObstruction.groundLeftAmplitude_positive` with the arguments shown in the
proof.
-/
theorem signedJost_at_ground {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (hM : Integrable (fun y => exp (-y)*m y)) (x : ℝ) :
    signedJost hm (-groundParameter hm hn) x=exp (-x)*H1.rep G.u x/groundLeftAmplitude G := by
  have he := congrArg (fun f : VolterraSpace => f x) (groundLeft_eq_signedJost G hM)
  change exp (-x)*H1.rep G.u x=groundLeftAmplitude G*signedJost hm (-groundParameter hm hn) x at he
  exact (eq_div_iff (groundLeftAmplitude_positive G hM).ne').mpr (by linarith)

end
end «2610.05164v2».LocalObstruction

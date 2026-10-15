import «2610.05164v2».LocalObstruction.VolterraBanach

/-!
Article: 2610.05164v2, Theorem 6.1.
Fubini duality for the actual causal Volterra kernel.
Use: `«2610.05164v2».LocalObstruction.volterra_pairing_swap` feeds
`«2610.05164v2».LocalObstruction.volterra_variation_mass` (volterra variation mass).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Exact identity `volterraKernel x y=max 0 (1-exp (-2*(x-y)))`.

Use: `«2610.05164v2».LocalObstruction.volterraKernel_joint_continuous` rewrites with this
identity to establish continuity of the displayed function: `Continuous (fun p : ℝ × ℝ =>
volterraKernel p.1 p.2)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem volterraKernel_max (x y : ℝ) :
    volterraKernel x y=max 0 (1-exp (-2*(x-y))) := by
  -- Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hy : y<x
  · have hn : 0≤1-exp (-2*(x-y)) := by
      have h := exp_le_one_iff.mpr (show -2*(x-y)≤0 by linarith)
      linarith
    simp only [volterraKernel, Set.indicator_of_mem (show y∈Iio x from hy), max_eq_right hn]
  · have hn : 1-exp (-2*(x-y))≤0 := by
      have h := one_le_exp (show 0≤-2*(x-y) by linarith)
      linarith
    simp only [volterraKernel, Set.indicator_of_notMem (show y∉Iio x from hy), max_eq_left hn]

 /--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => volterraKernel p.1 p.2)`.

Use: `«2610.05164v2».LocalObstruction.volterra_pair_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun p : ℝ × ℝ => a
p.1*volterraKernel p.1 p.2*b p.2) (volume.prod volume)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.volterraKernel_max` with
the arguments shown in the proof.
-/
theorem volterraKernel_joint_continuous : Continuous (fun p : ℝ × ℝ => volterraKernel p.1 p.2) := by
  simp_rw [volterraKernel_max]
  fun_prop

 /--
Integrability of the displayed function: `Integrable (fun p : ℝ × ℝ => a p.1*volterraKernel p.1
p.2*b p.2) (volume.prod volume)`.

Use: `«2610.05164v2».LocalObstruction.volterra_pairing_swap` uses this integrability result to
establish the precise assertion is `(∫ x,a x*(∫ y,volterraKernel x y*b y))= ∫ y,b y*(∫
x,volterraKernel x y*a x)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.volterraKernel_joint_continuous`,
`«2610.05164v2».LocalObstruction.volterraKernel_bounds` with the arguments shown in the proof.
-/
theorem volterra_pair_integrable {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    Integrable (fun p : ℝ × ℝ => a p.1*volterraKernel p.1 p.2*b p.2) (volume.prod volume) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».LocalObstruction.volterraKernel_joint_continuous`,
  -- `«2610.05164v2».LocalObstruction.volterraKernel_bounds` with the arguments shown in the
  -- proof.
  apply (ha.norm.mul_prod hb.norm).mono'
  · exact (ha.aestronglyMeasurable.comp_fst.mul
      volterraKernel_joint_continuous.aestronglyMeasurable).mul hb.aestronglyMeasurable.comp_snd
  · exact Filter.Eventually.of_forall (fun p => by
      rw [norm_mul,norm_mul,Real.norm_eq_abs (volterraKernel _ _),abs_of_nonneg (volterraKernel_bounds p.1 p.2).1]
      have h := mul_le_of_le_one_right (norm_nonneg (a p.1)) (volterraKernel_bounds p.1 p.2).2
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _))

 /--
The precise assertion is `(∫ x,a x*(∫ y,volterraKernel x y*b y))= ∫ y,b y*(∫ x,volterraKernel x
y*a x)`.

Use: `«2610.05164v2».LocalObstruction.volterra_adjoint_identity` uses this identity to
establish the precise assertion is `(∫ x,m x*R x*p x)-(∫ x,m x*p x)= ∫ x,m x*R x*volterra s m p
x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Establish the required integrability/summability obligations before exchanging integrals
or sums. Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem volterra_pairing_swap {a b : ℝ → ℝ} (ha : Integrable a) (hb : Integrable b) :
    (∫ x,a x*(∫ y,volterraKernel x y*b y))=
      ∫ y,b y*(∫ x,volterraKernel x y*a x) := by
  -- Establish the required integrability/summability obligations before exchanging integrals
  -- or sums.
  have h := integral_integral_swap (f := fun x y => a x*volterraKernel x y*b y) (volterra_pair_integrable ha hb)
  have hL : (∫ x,∫ y,a x*volterraKernel x y*b y)=
      ∫ x,a x*(∫ y,volterraKernel x y*b y) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by ring))
  have hR : (∫ y,∫ x,a x*volterraKernel x y*b y)=
      ∫ y,b y*(∫ x,volterraKernel x y*a x) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring))
  rw [hL,hR] at h
  exact h

end
end «2610.05164v2».LocalObstruction

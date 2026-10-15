import «2610.05164v2».LocalObstruction.GroundVolterraKernel

/-!
Article: 2610.05164v2, Theorem 6.1.
Reflection preserves the actual positive ground state of an even density.
Use: `«2610.05164v2».LocalObstruction.ground_even` feeds
`«2610.05164v2».LocalObstruction.groundJost_product` (ground Jost product).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».GroundState «2610.05164v2».Sobolev «2610.05164v2».Continuum
open scoped InnerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Exact identity `H1.rep (densityOperator m u) x=∫ y,exp (-|x-y|)*(m y*H1.rep u y)`.

Use: `«2610.05164v2».LocalObstruction.ground_even` rewrites with this identity to establish
exact identity `H1.rep G.u (-x)=H1.rep G.u x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem densityOperator_rep {m : ℝ → ℝ} (hm : Integrable m) (u : H1) (x : ℝ) :
    H1.rep (densityOperator m u) x=∫ y,exp (-|x-y|)*(m y*H1.rep u y) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  unfold H1.rep causalValue
  rw [densityOperator_inner hm,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [feature_inner,abs_sub_comm x y]
    ring)

 /--
Exact identity `H1.rep (convolution (fun y => j (-y))) x=H1.rep (convolution j) (-x)`.

Use: `«2610.05164v2».LocalObstruction.ground_even` rewrites with this identity to establish
exact identity `H1.rep G.u (-x)=H1.rep G.u x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem convolution_reflect_rep {j : ℝ → ℝ} (hj : Integrable j) (x : ℝ) :
    H1.rep (convolution (fun y => j (-y))) x=H1.rep (convolution j) (-x) := by
  rw [convolution_rep hj.comp_neg,convolution_rep hj,
    ← integral_neg_eq_self (fun y => exp (-|-x-y|)*j y) volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    rw [show -x- -y= -(x-y) by ring,abs_neg])

 /--
Exact identity `H1.rep G.u (-x)=H1.rep G.u x`.

Use: `«2610.05164v2».LocalObstruction.groundJost_product` rewrites with this identity to
establish the precise assertion is `signedJost hm (-groundParameter hm hn) x*signedJost hm
(-groundParameter hm hn) (-x)= (H1.rep G.u x)^2/(groundLeftAmplitude G)^2`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem ground_even {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ x,0≤m x}
    (G : GroundWitness hm hn) (he : ∀ x,m (-x)=m x) (x : ℝ) :
    H1.rep G.u (-x)=H1.rep G.u x := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let v := convolution (fun y => groundSource G (-y))
  have hv (y : ℝ) : H1.rep v y=H1.rep G.u (-y) := by
    rw [convolution_reflect_rep (groundSource_integrable G)]
    exact (ground_source_rep G (-y)).symm
  have hve : densityOperator m v=kernelEigenvalue hm hn 0 • v := by
    apply H1.rep_injective
    funext y
    rw [densityOperator_rep hm,H1.rep_smul]
    dsimp only
    rw [hv y]
    have hg := congrArg (fun f : H1 => H1.rep f (-y)) G.eigen
    rw [densityOperator_rep hm,H1.rep_smul] at hg
    dsimp only at hg
    rw [← hg,← integral_neg_eq_self (fun z => exp (-|-y-z|)*(m z*H1.rep G.u z)) volume]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      dsimp only
      rw [hv,he,show -y- -z= -(y-z) by ring,abs_neg])
  have hz : (∫ y,(H1.slope v y-G.R.a y*H1.rep v y)^2)=0 := by
    rw [G.R.square_identity hm,density_ground_energy hm hn G.mass_positive hve,sub_self]
  obtain ⟨r,hr⟩ := (G.R.residual_integral_eq_zero_iff_smul G.positive G.derivative v).mp hz
  have hr1 : r=1 := by
    have h := hv 0
    rw [hr,H1.rep_smul,neg_zero] at h
    nlinarith [G.positive 0]
  rw [hr1,one_smul] at hr
  rw [← hv x,hr]

end
end «2610.05164v2».LocalObstruction

import «2610.05164v2».LocalObstruction.OperatorPerturbation
import «2610.05164v2».GroundState.Article
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
Article: 2610.05164v2, Theorem 6.1.
The actual ground coupling is the reciprocal norm of the positive density operator.
Use: `«2610.05164v2».LocalObstruction.groundCoupling_finite_continuousAt` feeds
`«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` (ground Coupling finite c1).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Continuum «2610.05164v2».GroundState «2610.05164v2».Sobolev
open scoped InnerProductSpace Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Exact identity `‖densityOperator m‖=kernelEigenvalue hm hn 0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_actual` rewrites with this identity to
establish exact identity `groundCoupling m=groundParameter hm hn`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Separate `f=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem densityOperator_norm_eq_top {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) (hM : 0<∫ x,m x) : ‖densityOperator m‖=kernelEigenvalue hm hn 0 := by
  -- Separate `f=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let D := densitySpectralData hm hn
  have hp := densityOperator_positive hm hn
  obtain ⟨hl,u,hu,he⟩ := top_density_attained hm hn hM
  apply le_antisymm
  · rw [(densityOperator m).norm_eq_iSup_rayleighQuotient hp.isSymmetric]
    apply ciSup_le
    intro f
    by_cases hf : f=0
    · simp [hf,hl.le]
    have hb := D.top_quadratic_bound f
    rw [density_kernel_eigenvalue_eq hm hn D] at hb
    have hnq : 0 ≤ inner ℝ f (densityOperator m f) := by
      simpa only [RCLike.re_to_real] using hp.re_inner_nonneg_right f
    rw [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real,real_inner_comm,abs_of_nonneg (div_nonneg hnq (sq_nonneg _))]
    exact (div_le_iff₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hf))).mpr hb
  · have hb := (densityOperator m).le_opNorm u
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos hl,hu,mul_one,mul_one] at hb
    exact hb

 /--
Defines `groundCoupling` of type `ℝ` by `2/‖densityOperator m‖`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_actual` rewrites with this definition to
establish exact identity `groundCoupling m=groundParameter hm hn`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def groundCoupling (m : ℝ → ℝ) : ℝ := 2/‖densityOperator m‖

 /--
Exact identity `groundCoupling m=groundParameter hm hn`.

Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.densityOperator_norm_eq_top` with the arguments shown in the
proof.
-/
theorem groundCoupling_actual {m : ℝ → ℝ} (hm : Integrable m)
    (hn : ∀ x,0≤m x) (hM : 0<∫ x,m x) : groundCoupling m=groundParameter hm hn := by rw [groundCoupling,densityOperator_norm_eq_top hm hn hM,groundParameter]

 /--
Continuity at the stated point: `ContinuousAt (fun a : ι → ℝ => groundCoupling (perturb m v a))
0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` uses this continuity result to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling
(perturb m v a)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundCoupling_finite_continuousAt {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    (hM : 0<∫ x,m x) (hv : ∀ i,Integrable (v i)) :
    ContinuousAt (fun a : ι → ℝ => groundCoupling (perturb m v a)) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun a : ι → ℝ => densityOperator (perturb m v a))=
      fun a => densityOperator m+∑ i,a i • densityOperator (v i) := by
    funext a
    exact densityOperator_perturb hm hv a
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun a : ι → ℝ => densityOperator (perturb m v a)) := by
    rw [he]
    fun_prop
  apply continuousAt_const.div hc.continuousAt.norm
  have hz : perturb m v (0:ι → ℝ)=m := by funext x;simp [perturb]
  rw [hz,densityOperator_norm_eq_top hm hn hM]
  exact (top_density_attained hm hn hM).1.ne'

end
end «2610.05164v2».LocalObstruction

import «2610.05164v2».LocalObstruction.GroundTransmission
import «2610.05164v2».LocalObstruction.GroundNorm
import «2610.05164v2».LocalObstruction.TransmissionAnalytic

/-!
Article: 2610.05164v2, Theorem 6.1.
The continuous actual ground coupling, rather than a chosen zero, solves the analytic transmission
equation for every sufficiently small compact family.
Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` feeds
`«2610.05164v2».LocalObstruction.single_ground_root_near` (single ground root near).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».GroundState
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
The stated quantitative bound `0<∫ x,m x`.

Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.density_mass_positive` with the
arguments shown in the proof.
-/
theorem positive_continuous_mass {m : ℝ → ℝ} (hm : Integrable m)
    (hc : Continuous m) (hn : ∀ x,0<m x) : 0<∫ x,m x := by
  apply density_mass_positive hm (fun x => (hn x).le)
  intro hz
  have heq : m=0 := (hc.ae_eq_iff_eq volume continuous_zero).mp hz
  exact (hn 0).ne' (congrFun heq 0)

 /--
Integrability of the displayed function: `Integrable (fun x => exp (-x)*perturb m v a x)`.

Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` uses this integrability result
to prove the eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝
0, perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem perturb_exponential_integrable {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hM : Integrable (fun x => exp (-x)*m x))
    (hc : ∀ i,Continuous (v i)) (hs : ∀ i,HasCompactSupport (v i)) (a : ι → ℝ) :
    Integrable (fun x => exp (-x)*perturb m v a x) := by
  -- Establish hi as the integrability justification for the later integral estimates or
  -- changes of order.
  have hi (i : ι) : Integrable (fun x => exp (-x)*v i x) :=
    ((continuous_exp.comp continuous_neg).mul (hc i)).integrable_of_hasCompactSupport (hs i).mul_left
  have he : (fun x => exp (-x)*perturb m v a x)=
      fun x => exp (-x)*m x+∑ i,a i*(exp (-x)*v i x) := by
    funext x
    unfold perturb
    rw [mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact hM.add (integrable_finsetSum _ (fun i _ => (hi i).const_mul (a i)))

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` uses this identity to establish
smoothness to the stated order: `ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling (perturb m v
a)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral.
-/
theorem actual_ground_root_near {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hM : Integrable (fun x => exp (-x)*m x))
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i)) (hvcomp : ∀ i,HasCompactSupport (v i)) :
    ∀ᶠ a : ι → ℝ in 𝓝 0,
      perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [finite_perturbation_positive hc hn hvc hvcomp] with a ha
  -- Establish continuity hpc before using the function at limits or in calculus arguments.
  have hpc : Continuous (perturb m v a) := by unfold perturb;fun_prop
  have hpi := perturb_integrable hm hv a
  have hpn := fun x => (ha x).le
  have hmass := positive_continuous_mass hpi hpc ha
  have hne : ¬perturb m v a=ᵐ[volume] 0 := by
    intro hz
    have hzero : (∫ x,perturb m v a x)=0 := by rw [integral_congr_ae hz];simp
    exact hmass.ne' hzero
  let G := Classical.choice (ground_state hpi hpn hne)
  rw [perturbTransmission_signed_actual,
    groundCoupling_actual hpi hpn hmass]
  exact signedTransmission_at_ground G (perturb_exponential_integrable hM hvc hvcomp a)

end
end «2610.05164v2».LocalObstruction

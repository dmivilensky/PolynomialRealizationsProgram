import «2610.05164v2».LocalObstruction.GroundFiniteRoots
import «2610.05164v2».LocalObstruction.ScalarImplicit

/-!
Article: 2610.05164v2, Theorem 6.1.
Lemma 26(ii): the actual ground parameter is C1 near every positive even base with a left
exponential moment, under finite compact density variations.
Use: `«2610.05164v2».LocalObstruction.groundCoupling_finite_c1` feeds
`«2610.05164v2».LocalObstruction.groundCoupling_single_c1` (ground Coupling single c1).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».GroundState
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Smoothness to the stated order: `ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling (perturb m v
a)) 0`.

Use: `«2610.05164v2».LocalObstruction.groundCoupling_single_c1` uses this identity to establish
smoothness to the stated order: `ContDiffAt ℝ 1 (fun ε : ℝ => groundCoupling (m+ε • v)) 0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundCoupling_finite_c1 {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hM : Integrable (fun x => exp (-x)*m x)) (he : ∀ x,m (-x)=m x)
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i)) (hvcomp : ∀ i,HasCompactSupport (v i)) :
    ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling (perturb m v a)) 0 := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hmass := positive_continuous_mass hm hc hn
  have hnp := fun x => (hn x).le
  have hne : ¬m=ᵐ[volume] 0 := by
    intro hz
    have hm0 : (∫ x,m x)=0 := by rw [integral_congr_ae hz];simp
    exact hmass.ne' hm0
  let G := Classical.choice (ground_state hm hnp hne)
  let K := fun a : ι → ℝ => groundCoupling (perturb m v a)
  have hz : perturb m v (0:ι → ℝ)=m := by funext x;simp [perturb]
  have hk : K 0=groundParameter hm hnp := by
    dsimp only [K]
    rw [hz,groundCoupling_actual hm hnp hmass]
  let c := (1/2:ℝ)*(∫ x,m x*signedJost hm (-groundParameter hm hnp) x*
    signedJost hm (-groundParameter hm hnp) (-x))
  have hcpos : 0<c := mul_pos (by norm_num) (groundTransmission_scale_positive G hM)
  have hT0 : (fun t : ℝ => perturbTransmission hm hv ((0:ι → ℝ),t))=signedTransmission hm := by
    funext t
    rw [perturbTransmission_signed_actual]
    congr 1
  have hd : HasDerivAt (fun t : ℝ => perturbTransmission hm hv ((0:ι → ℝ),t)) c (-K 0) := by
    rw [hT0,hk]
    exact signedTransmission_scale_derivative hm _ he
  have hbase : perturbTransmission hm hv ((0:ι → ℝ),-K 0)=0 := by
    change (fun t : ℝ => perturbTransmission hm hv ((0:ι → ℝ),t)) (-K 0)=0
    rw [hT0,hk]
    exact signedTransmission_at_ground G hM
  have hF : ContDiffAt ℝ 1 (perturbTransmission hm hv) ((0:ι → ℝ),-K 0) :=
    (perturbTransmission_signed_analytic hm hv _).contDiffAt
  -- Establish continuity hK before using the function at limits or in calculus arguments.
  have hK : ContinuousAt (fun a => -K a) 0 :=
    (groundCoupling_finite_continuousAt hm hnp hmass hv).neg
  have hzero : ∀ᶠ a : ι → ℝ in 𝓝 0,
      perturbTransmission hm hv (a,-K a)=perturbTransmission hm hv (0,-K 0) := by
    rw [hbase]
    exact actual_ground_root_near hm hc hn hM hv hvc hvcomp
  have hroot := contDiffAt_scalar_root hF hK hzero hd hcpos.ne'
  convert! hroot.neg using 1
  simp only [neg_neg,K]

end
end «2610.05164v2».LocalObstruction

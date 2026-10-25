import chebyshev2.LocalObstruction.VolterraSignedAnalytic
import chebyshev2.LocalObstruction.TransmissionVariation

/-!
Article: chebyshev2, Theorem 6.1.
Entire signed transmission families, including the neighborhood of the negative ground coupling used
by the implicit function theorem.
Use: `chebyshev2.LocalObstruction.perturbTransmission_signed_actual` feeds
`chebyshev2.LocalObstruction.single_ground_root_near` (single ground root near).
Proof chain: `chebyshev2.LocalObstruction.groundObservationWitness` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real chebyshev2.Filters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
The precise assertion is `AnalyticAt ℝ (perturbTransmission hm hv) p`.

Use: `chebyshev2.LocalObstruction.groundCoupling_finite_c1` uses this assertion to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling
(perturb m v a)) 0`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem perturbTransmission_signed_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) :
    AnalyticAt ℝ (perturbTransmission hm hv) p := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hsol := volterraSolution_signed_joint_analytic hm hv p
  apply analyticAt_const.add
  apply (analyticAt_snd.div_const (c := (2:ℝ))).mul
  apply ((volterraMass hm).analyticAt _ |>.comp (f := volterraSolution hm hv) hsol).add
  have hsum := Finset.analyticAt_sum Finset.univ (f := fun i (z : (ι → ℝ) × ℝ) =>
    z.1 i*volterraMass (hv i) (volterraSolution hm hv z)) (fun i _ =>
      (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt p.1).comp (f := fun p : (ι → ℝ) × ℝ => p.1) analyticAt_fst).mul
        (((volterraMass (hv i)).analyticAt _).comp (f := volterraSolution hm hv) hsol))
  convert! hsum using 1
  funext p
  simp only [Finset.sum_apply]

 /--
Exact identity `perturbTransmission hm hv p=signedTransmission (perturb_integrable hm hv p.1)
p.2`.

Use: `chebyshev2.LocalObstruction.actual_ground_root_near` rewrites with this identity to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.volterraMass_perturb` with
the arguments shown in the proof.
-/
theorem perturbTransmission_signed_actual {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hv : ∀ i,Integrable (v i))
    (p : (ι → ℝ) × ℝ) :
    perturbTransmission hm hv p=signedTransmission (perturb_integrable hm hv p.1) p.2 := by
  unfold perturbTransmission signedTransmission
  rw [← volterraMass_perturb hm hv p.1]
  rfl

end
end chebyshev2.LocalObstruction

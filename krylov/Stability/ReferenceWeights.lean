import krylov.Stability.WeightedNormalization
import krylov.Reference.Contraction

/-!
Article: main_krylov, apB:lem:UAsteps, true CG weights at arbitrarily small steps.
Use: discharge the reference nonstagnation ratio from actual CG energies and
apply the weighted normalization mechanism without a minimum-energy denominator.
Source: the already proved actual CG energy drop and positive-interval contraction.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The genuine canonical CG error norms decrease throughout the actual totalized run.
Use: every later remaining-error weight is bounded by an earlier actual reference error.
Article: main_krylov, apB:lem:UAsteps and apB:lem:nostag.
Proof: each exact actual energy drop is the nonnegative squared norm of its actual canonical step. -/
theorem cgError_antitone (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) : Antitone (fun k => ‖cgCanonicalError base g k‖) := by
  apply antitone_nat_of_succ_le
  intro k
  have hd := cgEnergy_drop base hb g k
  rw [cgEnergy_eq_norm_sq base hb] at hd
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖canonicalCGStep base g k‖]

/-- A later actual CG error is controlled by the true earlier canonical step with only the spectral condition ratio.
Use: the printed uniform flag argument needs no lower bound on individual reference step energies.
Article: main_krylov, apB:lem:UAsteps, ‖ê_k‖/√c_j≤√κ.
Proof: actual error monotonicity reduces to time j; the proved actual positive-interval
energy-drop lower bound then supplies the step/error ratio, including arbitrarily small nonzero steps. -/
theorem cgError_step_ratio (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {j k : ℕ} (hj : j<referenceAtomCount base hb g) (hjk : j≤k) :
    ‖cgCanonicalError base g k‖≤Real.sqrt (upper/mu)*‖canonicalCGStep base g j‖ := by
  -- Keep the actual step norm as the weight throughout the spectral comparison.
  have hu : 0<upper := hm.trans_le hmu
  have hd := cgEnergy_lower_condition base hb g hm hmu hspec hj
  rw [cgEnergy_eq_norm_sq base hb] at hd
  have hr : 0≤upper/mu := div_nonneg hu.le hm.le
  have he : ‖cgCanonicalError base g j‖^2≤(upper/mu)*‖canonicalCGStep base g j‖^2 := by
    calc
      _ = (upper/mu)*(mu/upper*‖cgCanonicalError base g j‖^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hd hr
  have hs : ‖cgCanonicalError base g j‖≤Real.sqrt (upper/mu)*‖canonicalCGStep base g j‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hr] using he
  exact (cgError_antitone base hb g hjk).trans hs

/-- Actual later CG errors uniformly weight normalized perturbed-step errors independently of all individual step lengths.
Use: applies the small-step mechanism to the actual reference, rather than an abstract reference-ratio assumption.
Article: main_krylov, apB:lem:UAsteps, weighted normalized-column comparison.
Proof: the true earlier CG step is nonzero and normalizes to its actual unit
direction; its actual nonstagnation ratio discharges the weighted normalization estimate. -/
theorem cg_weighted_normalization (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {j k : ℕ} (hj : j<referenceAtomCount base hb g) (hjk : j≤k)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x≠0) (ε : ℝ) (he : ‖x-canonicalCGStep base g j‖≤ε) :
    ‖cgCanonicalError base g k‖*‖NormedSpace.normalize x-canonicalCGUnitStep base g j‖≤
      2*Real.sqrt (upper/mu)*ε := by
  have hs := canonicalCGStep_ne_zero base hb g j (fun i hi => cg_nonstagnation base hb g i (hi.trans_lt hj))
  have hq : ‖canonicalCGUnitStep base g j‖=1 := NormedSpace.norm_normalize hs
  have he' : ‖x-‖canonicalCGStep base g j‖ • canonicalCGUnitStep base g j‖≤ε := by
    simpa only [canonicalCGUnitStep, NormedSpace.norm_smul_normalize] using he
  exact normalization_error_weight x _ hx hq _ _ _ ε (norm_pos_iff.mpr hs)
    (Real.sqrt_nonneg _) he' (cgError_step_ratio base hb g hm hmu hspec hj hjk)

/-- Actual later CG errors uniformly weight the genuine rank-one flag changes caused by perturbed steps.
Use: supplies the individual weighted projector terms in the source's near-breakdown flag estimate.
Article: main_krylov, apB:lem:UAsteps, τ_jτ_jᵀ−q_jq_jᵀ.
Proof: the exact rank-one difference costs twice the actual unit-direction
change; the proved actual-reference weighted normalization bound removes its small-step denominator. -/
theorem cg_weighted_rankOne (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {mu upper : ℝ} (hm : 0<mu) (hmu : mu≤upper)
    (hspec : ∀ i, mu≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤upper)
    {j k : ℕ} (hj : j<referenceAtomCount base hb g) (hjk : j≤k)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x≠0) (ε : ℝ) (he : ‖x-canonicalCGStep base g j‖≤ε) :
    ‖cgCanonicalError base g k‖*
      ‖InnerProductSpace.rankOne ℝ (NormedSpace.normalize x) (NormedSpace.normalize x)-
        InnerProductSpace.rankOne ℝ (canonicalCGUnitStep base g j) (canonicalCGUnitStep base g j)‖≤
      4*Real.sqrt (upper/mu)*ε := by
  have hs := canonicalCGStep_ne_zero base hb g j (fun i hi => cg_nonstagnation base hb g i (hi.trans_lt hj))
  have hp := unit_rankOne_difference (NormedSpace.normalize x) (canonicalCGUnitStep base g j)
    (NormedSpace.norm_normalize hx) (NormedSpace.norm_normalize hs)
  have hw := cg_weighted_normalization base hb g hm hmu hspec hj hjk x hx ε he
  have hb' := mul_le_mul_of_nonneg_left hp (norm_nonneg (cgCanonicalError base g k))
  nlinarith

end
end krylov.Stability

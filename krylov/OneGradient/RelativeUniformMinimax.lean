import krylov.OneGradient.ObservedPriorAttainment
import krylov.OneGradient.CentralFibreMinimax
import krylov.OneGradient.RelativeBallRatio
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant(b), original whole relative-ball minimax.
Use: one known-prior observed harmonic policy is chosen before every actual
information fibre meeting the known relative base ball, in either XRFC basis.
Source: genuine arbitrary-centre attained physical intervals and ratio bound,
the common observed-prior policy and the sharp central physical adversary.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
variable {n : ℕ}

/-- The known relative base-ball prior in original physical coordinates.
Use: membership is a known class predicate, with no unknown reference captured
by the observed policy; its actual candidate matrices are positive.
Article: main_krylov, cor:quant(b). -/
def relativeBallPrior (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (rho : ℝ) :
    Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  {A | relativeBudget center (A-center)≤rho}

/-- A single actual method uniformly controls every genuine information
fibre meeting the known relative ball and every admissible output matrix.
Use: the method is chosen before all original physical references and pivots.
Article: main_krylov, cor:quant(b). -/
def relativePriorGuarantee (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (rho : ℝ) (g : EuclideanSpace ℝ (Fin (n+1))) (omega : ℝ)
    (method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1)))) (v : ℝ) : Prop :=
  ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ),
    relativeBudget center (lanczosCompletion A hA g hg hc b-center)≤rho →
      ∀ B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,B.IsSymm →
        relativeBudget (lanczosCompletion A hA g hg hc b) (B-lanczosCompletion A hA g hg hc b)≤omega →
        fibreScenarioError A hA g hg hc method b B≤v

/-- One genuine observed endpoint policy uniformly attains rho times the
output radius on the whole known relative ball, in either native XRFC basis.
Use: the centre need not share the incoming information; arbitrary positive
earlier observed trials, collapsed intervals and zero radii are included.
Article: main_krylov, cor:quant(b), original prior-wide upper bound.
Proof: each actually met fibre has a true attained compact pivot interval.
Every admitted endpoint is positive. The same original observed-prior rule
is its exact harmonic trial; the genuine arbitrary-centre ratio bound makes
its true fixed-fibre coefficient at most rho. -/
theorem xrfc_relative_prior_guarantee (directions : Bool)
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho < 1) (g : EuclideanSpace ℝ (Fin (n+1)))
    (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ) (he : ∀ H,0 < earlier H)
    {omega : ℝ} (homega : 0≤omega) :
    relativePriorGuarantee center rho g omega
      (xrfcBasisMethod directions (observedPriorLastTrial n (relativeBallPrior center rho) earlier)) (rho*omega) := by
  intro A hA hg hc b hb B hB hbudget
  obtain ⟨lo,hi,horder,hinterval⟩ := relative_ball_fibre_interval A hA g hg hc center hcenter rho ⟨b,hb⟩
  have hblo := (hinterval lo).mpr ⟨le_rfl,horder⟩
  have hbhi := (hinterval hi).mpr ⟨horder,le_rfl⟩
  have hlo := relative_ball_fibre_positive A hA g hg hc center hcenter hrho hsmall lo hblo
  have hvalue := relative_ball_fibre_trial_value A hA g hg hc center hcenter hrho hsmall lo hi hblo hbhi
  have hout := xrfc_observed_prior_fibre_upper directions A hA g hg hc (relativeBallPrior center rho) lo hi
    hlo horder hinterval earlier he homega b ((hinterval b).mp hb) B hB hbudget
  have hh := mul_le_mul_of_nonneg_left hvalue homega
  exact hout.trans (by simpa only [mul_comm] using hh)

/-- The complete original prior-wide relative-ball minimax is rho times the
output radius, attained by one genuine observed harmonic XRFC policy.
Use: the centre's original full-atom data supply the actual two central
endpoint adversaries for every competing method, with no consistency premise.
Article: main_krylov, cor:quant(b).
Proof: the single observed-prior policy gives a uniform guarantee before all
fibre quantifiers. Restricting any competing uniform guarantee to the true
central information fibre invokes its proved sharp arbitrary-method minimum. -/
theorem relative_prior_exact_uniform_minimax
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    {rho omega : ℝ} (hrho : 0≤rho) (hrhosmall : rho < 1) (homega : 0≤omega) (homegasmall : omega≤1) :
    IsLeast {v : ℝ | ∃ method : OneGradientMethod (EuclideanSpace ℝ (Fin (n+1))),
      OneGradientSpanRestricted method ∧ relativePriorGuarantee center rho g omega method v} (rho*omega) := by
  constructor
  · let method := xrfcBasisMethod false (observedPriorLastTrial n (relativeBallPrior center rho) (fun _ => 1))
    refine ⟨method,xrfcMethod_spanRestricted fullMemory _,?_⟩
    exact xrfc_relative_prior_guarantee false center hcenter hrho hrhosmall g (fun _ => 1) (fun _ => zero_lt_one) homega
  · rintro v ⟨method,hm,hv⟩
    exact (central_fibre_exact_minimax center hcenter g hg hc hrho hrhosmall homega homegasmall).2
      ⟨method,hm,hv center hcenter hg hc⟩

/-- At the true centre's observed data the single prior-wide harmonic rule is
exactly the original centre's last genuine CG length.
Use: the source's central calibration is a property of the implemented
history-only rule, not an independently hard-coded fibre trial.
Article: main_krylov, cor:quant(b).
Proof: the actual central relative-budget interval has the source endpoints;
the original observed dictionary gives its harmonic trial, and the proved
central reciprocal-pivot calculation identifies the true central CG line. -/
theorem observed_relative_ball_central_trial
    (center : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hcenter : center.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues center hcenter.1 g).card=n+1)
    {rho : ℝ} (hrho : 0≤rho) (hsmall : rho < 1)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator center) g i)≠0) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator center) g n
    observedPriorHarmonic (relativeBallPrior center rho) H=CG.length (cgOperator center) g n := by
  let h := lastInversePivot center hcenter g hg hc
  let b0 := lastJacobiPivot center hcenter g hg hc
  obtain ⟨hlo,horder,_,hharmonic⟩ := central_fibre_parameters center hcenter g hg hc hrho hsmall
  have hinterval (b : ℝ) : lanczosCompletion center hcenter g hg hc b∈relativeBallPrior center rho ↔
      b∈Set.Icc (b0-rho/h) (b0+rho/h) := lanczos_completion_central_ball center hcenter g hg hc rho b
  exact (xrfc_observed_prior_harmonic center hcenter g hg hc trial ht (relativeBallPrior center rho)
    (b0-rho/h) (b0+rho/h) hlo horder hinterval).2.trans hharmonic

end
end krylov.OneGradient

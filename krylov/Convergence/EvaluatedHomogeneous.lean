import krylov.Methods.EvaluatedLaunch
import krylov.Methods.VirtualScaling
import krylov.Methods.HomogeneousTrial

/-!
Article: main_krylov, prop:EL, primitive homogeneous evaluated launch.
Use: derive actual query and semantic-output scaling from the genuine
degree-zero observed trial rule; no native trajectory scaling is assumed.
Source: real one-gradient induction and virtual block covariance.
-/
namespace krylov.Convergence
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual evaluated-launch query and gradient scales under the
primitive degree-zero observed trial rule. Article: prop:EL. -/
theorem evaluatedLaunch_scalar_prefix (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    let m := evaluatedLaunchMethod trial (E := E)
    (∀ k≤N, oneGradientGradient m A (c • g) k=c • oneGradientGradient m A g k) ∧
      ∀ i<N, oneGradientStep m A (c • g) i=c • oneGradientStep m A g i := by
  -- Both the genuine observation chart and real virtual solves are compared at the same actual finite prefix.
  let m := evaluatedLaunchMethod trial (E := E)
  change (∀ k≤N, oneGradientGradient m A (c • g) k=c • oneGradientGradient m A g k) ∧ _
  induction N with
  | zero =>
    refine ⟨?_,by intro i hi; omega⟩
    intro k hk
    have he : k=0 := by omega
    subst k
    rfl
  | succ k ih =>
    have hV := oneGradient_virtualBlock_scalar m A g k c hc.ne' ih.2 (ih.1 k le_rfl)
    simp only [selectedWindow_full] at hV
    have hτ := oneGradient_trial_scalar trial ht m A g k c hc ih.2 ih.1
    have hs : oneGradientStep m A (c • g) k=c • oneGradientStep m A g k := by
      change trial _ • windowDirection _ (virtualGradient _ _)=c • _
      rw [hV.2.2,hτ,smul_comm]
      rfl
    have hnext : oneGradientGradient m A (c • g) (k+1)=c • oneGradientGradient m A g (k+1) := by
      simp only [oneGradientGradient_succ,ih.1 k le_rfl,hs,map_smul,smul_add]
    constructor
    · intro j hj
      by_cases he : j=k+1
      · subst j; exact hnext
      · exact ih.1 j (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i; exact hs
      · exact ih.2 i (by omega)

/-- The genuine unevaluated XRFC point and its semantic output gradient scale with the actual initial gradient under primitive degree-zero trials.
Use: the compact-reference output Taylor theorem extends to positive cones with unchanged constants.
Article: main_krylov, lem:U(c,d), actual homogeneous XRFC outputs.
Proof: the proved real prefix scaling applies to every actual physical query;
its finite sum scales the evaluated displacement, the genuine final virtual
correction scales as well, and the true linear output operator scales its
semantic gradient without adding any observation. -/
theorem evaluatedLaunch_scalar_output (trial : History E → ℝ) (ht : ObservedTrialHomogeneous trial)
    (A : ℕ → E →L[ℝ] E) (B : E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    let m := evaluatedLaunchMethod trial (E := E)
    let H := oneGradientRun m A g N
    let Hc := oneGradientRun m A (c • g) N
    m.outputDisplacement Hc=c • m.outputDisplacement H ∧
      m.outputGradient B Hc=c • m.outputGradient B H := by
  -- The final virtual output is only a real data-only displacement, so its scaling spends no extra query.
  let m := evaluatedLaunchMethod trial (E := E)
  have hp := evaluatedLaunch_scalar_prefix trial ht A g c hc N
  have hv := oneGradient_virtualBlock_scalar m A g N c hc.ne' hp.2 (hp.1 N le_rfl)
  simp only [selectedWindow_full] at hv
  have hd : (oneGradientRun m A (c • g) N).displacement=c • (oneGradientRun m A g N).displacement := by
    simp only [oneGradientRun_displacement_sum,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi => hp.2 i (Finset.mem_range.mp hi)
  constructor
  · change (oneGradientRun m A (c • g) N).displacement+virtualCorrection _ _=c • _
    rw [hd,hv.1,← smul_add]
    rfl
  · change oneGradientGradient m A (c • g) N+B (virtualCorrection _ _)=c • _
    rw [hp.1 N le_rfl,hv.1,map_smul,← smul_add]
    rfl


end
end krylov.Convergence

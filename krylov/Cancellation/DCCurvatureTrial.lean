import krylov.Cancellation.DCOneGradientTrajectory
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef and thm:dcs(b), original curvature-based DC trials.
Use: read the untilted observed direction and virtual gradient before forming
the tilted solve, and derive the printed genuine effective curvature trial.
Source: actual native quadratic flag induction, Galerkin virtual reference
and the original exact CG search identity.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed descent pairing used by the original curvature trial.
Use: the untilted direction and virtual gradient are computed before any
estimate is inserted into the genuine tilted direction.
Article: main_krylov, s8:dcsdef, -ghat^T dFC. -/
def dcCurvatureSlope (memory : ℕ → ℕ) (H : History E) : ℝ :=
  -inner ℝ (virtualGradient (selectedWindow memory H) H.gradient)
    (windowDirection (selectedWindow memory H) H.gradient)

/-- The original data-only curvature trial for an observed directional
curvature estimate, evaluated before the tilted direction is formed.
Use: instantiate both real DC executors with the source's curvature rule.
Article: main_krylov, s8:dcsdef, tau=-ghat^T dFC/chat. -/
def dcCurvatureEstimate (memory : ℕ → ℕ) (curvature : History E → ℝ) : History E → ℝ :=
  fun H => dcCurvatureSlope memory H/curvature H

/-- Positive original observed slope and curvature give a positive actual estimate.
Use: the curvature rule supplies the genuine nonzero-estimate source domain.
Article: main_krylov, s8:dcsdef.
Proof: divide the real strictly positive observed descent pairing by the
strictly positive chosen observed curvature. -/
theorem dc_curvature_estimate_positive (memory : ℕ → ℕ) (curvature : History E → ℝ) (H : History E)
    (hq : 0<dcCurvatureSlope memory H) (hc : 0<curvature H) :
    0<dcCurvatureEstimate memory curvature H := div_pos hq hc

/-- On a genuine actual one-gradient quadratic DC prefix the observed untilted
direction and virtual gradient have their original derived reference values.
Use: specialize curvature policies on real execution without assuming either
virtual consistency or a scaled direction formula.
Article: main_krylov, thm:dcs(b).
Proof: the actual execution induction supplies the true independent full flag
and incoming-gradient decomposition. Genuine Galerkin and conjugacy uniqueness
then identify the two original native observed computations. -/
theorem dc_one_gradient_curvature_inputs (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let H := oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k
    virtualGradient (selectedWindow fullMemory H) H.gradient=CG.gradient Q g k ∧
      windowDirection (selectedWindow fullMemory H) H.gradient=
        dcIncomingFactor estimate Q g k • CG.direction Q g k := by
  let m := dcSlideOneGradient fullMemory estimate
  let H := oneGradientRun m (fun _ => Q) g k
  obtain ⟨_,hLI,hspan,v,hv,hgrad⟩ := dc_one_gradient_state estimate Q hQ hpos g N hpre ht k hk
  have hprefix : ∀ i<k,CG.gradient Q g i≠0 := fun i hi => hpre i (hi.trans_le hk)
  have hy : ∀ i,windowImages H.pairs i=Q (windowSteps H.pairs i) := fun i =>
    oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  dsimp only
  rw [selectedWindow_full]
  exact ⟨(virtual_reference_basis H Q hQ hpos g k hprefix
    (oneGradientRun_quadratic_gradient m Q g k) hy hLI hspan).2.1,
    windowDirection_scaled_reference H.pairs Q hQ hpos g k hprefix hy hLI hspan
      (dcIncomingFactor estimate Q g k) v H.gradient hv hgrad⟩

/-- The real original curvature-based one-gradient DC effective length has
precisely the article's CG-energy-over-observed-curvature formula.
Use: identify the genuine relative trial error on the actual XRFC reference
trajectory, with the source curvature read from its true observed history.
Article: main_krylov, thm:dcs(b), t_k=alpha_k rho_k^2 d_k^T Q d_k/chat_k.
Proof: genuine native virtual inputs give the actual slope rho times the true
CG descent pairing. The proved positive actual CG curvature cancels in the
original exact-search length, and the true evaluated-length definition gives
the printed squared-scale curvature trial. -/
theorem dc_one_gradient_curvature_length (curvature : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<dcCurvatureEstimate fullMemory curvature (oneGradientRun
      (dcSlideOneGradient fullMemory (dcCurvatureEstimate fullMemory curvature)) (fun _ => Q) g i))
    (k : ℕ) (hk : k<N) :
    let estimate := dcCurvatureEstimate fullMemory curvature
    let H := oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k
    let rho := dcIncomingFactor estimate Q g k
    dcEvaluatedLength estimate Q g k=
      CG.length Q g k*rho^2*inner ℝ (CG.direction Q g k) (Q (CG.direction Q g k))/curvature H := by
  let estimate := dcCurvatureEstimate fullMemory curvature
  let H := oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g k
  let rho := dcIncomingFactor estimate Q g k
  have hinputs := dc_one_gradient_curvature_inputs estimate Q hQ hpos g N hpre ht k hk.le
  have hInv := CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))
  have hd : CG.direction Q g k≠0 := (CG.invariant_line_pos Q hpos g k hInv (hpre k hk)).1
  have he : inner ℝ (CG.direction Q g k) (Q (CG.direction Q g k))≠0 := (hpos _ hd).ne'
  have hslope : dcCurvatureSlope fullMemory H=
      rho*(-inner ℝ (CG.direction Q g k) (CG.gradient Q g k)) := by
    unfold dcCurvatureSlope
    rw [hinputs.1,hinputs.2,real_inner_smul_right,real_inner_comm (CG.gradient Q g k)]
    ring
  change (dcCurvatureSlope fullMemory H/curvature H)*rho=_
  rw [hslope]
  change _=(-inner ℝ (CG.direction Q g k) (CG.gradient Q g k)/
    inner ℝ (CG.direction Q g k) (Q (CG.direction Q g k)))*rho^2*
      inner ℝ (CG.direction Q g k) (Q (CG.direction Q g k))/curvature H
  field_simp

end
end krylov.Cancellation

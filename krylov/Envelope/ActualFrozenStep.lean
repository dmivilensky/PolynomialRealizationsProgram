import krylov.Envelope.ActualFiltration

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:tilt and apB:eq:nu, actual frozen step congruence.
Use: identify the true actual step derivative with the genuine frozen
displacement increment modulo its real next Krylov flag, before
differentiating actual observed step-gradient residuals.
Source: complete actual raw-method frozen filtration, genuine compatible
gradient-coordinate lifts and the real measured frozen step identity.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine smooth source-admissible globally CG-consistent raw recorded step derivative differs from the actual frozen displacement increment only in its true next Krylov flag.
Use: Every genuine smooth source-admissible globally CG-consistent raw recorded step derivative differs from the actual frozen displacement increment only in its true next Krylov flag.
Article: main_krylov, apB:eq:tilt and apB:eq:nu, actual frozen step congruence.
Proof: The actual gradient remainder is a genuine reference-operator image of the true preceding Krylov flag. Its real coordinate lift remains in the actual next flag; combine genuine raw step coherence with the proved measured frozen step lift and the true frozen displacement increment. -/
theorem actual_frozen_step (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hpre : ∀ i<N, CG.gradient Q g i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (k : ℕ) (hk : k<N) :
    let ζ := referenceInjection Q g A
    deriv (fun t => probedStep m (A t) (B t) g k) 0-
      (frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ (k+1)-
        frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k)∈CG.krylovSpace Q g (k+1) := by
  -- Actual gradient derivatives and the true frozen response are compared through their genuine reference-gradient coordinate lifts.
  let δg := fun i => deriv (fun t => probedGradient m (A t) (B t) g i) 0
  let ζ := referenceInjection Q g A
  let F := fun i => frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ i 0
  have hfil := actual_frozen_filtration memory m hm hspan A B g Q hQ hpos hA0 hB0 N hA hB hpre hsmooth
  have hdiff (i : ℕ) (hi : i≤k) : δg i-F i∈CG.krylovSpace Q g (k+1) := by
    obtain ⟨v,hv,he⟩ := (hfil i (by omega)).2
    rw [← he]
    exact (krylovSpace_mono Q g (Nat.add_le_add_right hi 1)) (krylovSpace_operator Q g i hv)
  have hL := gradientJetLift_sub_mem Q g δg F k (CG.krylovSpace Q g (k+1)) hdiff (referenceStep Q g k)
  have hF := gradientJetLift_frozen_step Q hQ hpos g ζ k (fun i hi => hpre i (hi.trans_lt hk))
  change gradientJetLift Q g F k (referenceStep Q g k)=_ at hF
  have hs := actual_step_jet_coherence memory m hm hspan A B g Q hQ hpos hA0 hB0 N hA hB hpre hsmooth k hk
  have hsum := (CG.krylovSpace Q g (k+1)).add_mem hs hL
  -- The actual measured frozen step is exactly the genuine consecutive displacement difference.
  have hξ : frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ (k+1)-
      frozenDisplacement Q (CG.length Q g) (CG.beta Q g) ζ k=
        CG.length Q g k • frozenResponse Q (CG.length Q g) (CG.beta Q g) ζ k 1 := by
    rw [frozenDisplacement,Finset.sum_range_succ]
    exact add_sub_cancel_left _ _
  change _-_∈_
  rw [hξ,← hF]
  convert hsum using 1
  abel
end
end krylov.Envelope

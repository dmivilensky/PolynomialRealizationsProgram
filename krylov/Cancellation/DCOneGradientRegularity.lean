import krylov.Cancellation.DCOneGradientState
import krylov.Methods.DeferredReindex
import krylov.Methods.DataDeferredCoefficients
import krylov.Stability.TrialCoordinates
import krylov.Methods.VirtualCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs and lem:U(d), actual one-gradient DC regularity.
Use: derive genuine finite queried steps and returned gradients from primitive
smooth observed estimates, with every reference inverse domain discharged.
Source: actual chronological observation coordinates, native deferred-solve
regularity and the proved genuine full quadratic DC flag induction.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original full-memory tilted solve is exactly its genuine newest-age
array solve on the real one-gradient transcript.
Use: primitive finite calculus differentiates the actual executed decision.
Article: main_krylov, thm:dcs and lem:U(d).
Proof: the actual full window is its executed secant transcript; every list
column has its real chronological index, and the native solve reindexes exactly. -/
theorem oneGradient_full_deferred_coordinates (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g G : E) (a : ℝ) (k : ℕ) :
    deferredDirection (windowSteps (selectedWindow fullMemory (oneGradientRun m A g k)))
      (windowImages (selectedWindow fullMemory (oneGradientRun m A g k))) G a=
    deferredDirection (fun i : Fin k => oneGradientStep m A g (k-1-i.val))
      (fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val))) G a := by
  rw [oneGradient_full_window]
  let W := executedPairs (oneGradientStep m A g) (fun j => A j (oneGradientStep m A g j)) k
  let e : Fin W.length ≃ Fin k := finCongr (executedPairs_length _ _ k)
  have hs : windowSteps W=(fun i : Fin k => oneGradientStep m A g (k-1-i.val)) ∘ e := by
    funext i
    exact congrArg Prod.fst (executedPairs_get _ _ k i.val (by have hi := i.isLt; have he : W.length=k := executedPairs_length _ _ k; change i.val < W.length at hi; omega))
  have hy : windowImages W=(fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val))) ∘ e := by
    funext i
    exact congrArg Prod.snd (executedPairs_get _ _ k i.val (by have hi := i.isLt; have he : W.length=k := executedPairs_length _ _ k; change i.val < W.length at hi; omega))
  change deferredDirection (windowSteps W) (windowImages W) G a=_
  rw [hs,hy,deferredDirection_reindex]

/-- Every real one-gradient DC prefix has its genuine native inverse domain
at a positive nonstagnating quadratic reference with positive actual estimates.
Use: no matrix-domain assumption is added to the source regularity assertion.
Article: main_krylov, thm:dcs(b) and lem:U(d).
Proof: the actual execution induction proves the stored steps independent;
true quadratic secants make their native cross-Gram positive definite. Exact
chronological determinant coordinates give the real fixed finite array domain. -/
theorem dc_one_gradient_array_domain (estimate : History E → ℝ) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) g i))
    (k : ℕ) (hk : k≤N) :
    let m := dcSlideOneGradient fullMemory estimate
    (crossGram (fun i : Fin k => Q (oneGradientStep m (fun _ => Q) g (k-1-i.val)))
      (fun i : Fin k => oneGradientStep m (fun _ => Q) g (k-1-i.val))).det≠0 := by
  let m := dcSlideOneGradient fullMemory estimate
  let H := oneGradientRun m (fun _ => Q) g k
  have hLI := (dc_one_gradient_state estimate Q hQ hpos g N hpre ht k hk).2.1
  have hy : windowImages H.pairs=fun i => Q (windowSteps H.pairs i) := by
    funext i
    exact oneGradientRun_pairs_quadratic m Q g k (H.pairs.get i) (List.get_mem _ i)
  have hd : (crossGram (windowImages H.pairs) (windowSteps H.pairs)).det≠0 := by
    rw [hy]
    exact (operatorGram_posDef Q hQ hpos hLI).det_pos.ne'
  change (crossGram (windowImages (oneGradientRun m (fun _ => Q) g k).pairs)
    (windowSteps (oneGradientRun m (fun _ => Q) g k).pairs)).det≠0 at hd
  rw [oneGradientRun_pairs_segmentOperators,crossGram_executed_det] at hd
  exact hd

/-- The actual finite full-memory one-gradient DC execution is C-r on its
true native domains from the original primitive observed estimate charts.
Use: regularity is derived by real queries, without a supplied smooth trajectory.
Article: main_krylov, thm:dcs and lem:U(d).
Proof: compose the genuine primitive estimate with the actual finite observed
data. Differentiate the original tilted native solve, multiply by that same
chosen estimate, and apply the real next segment operator. Retain every true
returned gradient so the next original data-only estimate remains available. -/
theorem dc_one_gradient_prefix_contDiffAt {r : WithTop ℕ∞} (estimate : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ)
    (hA : ∀ i<N,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (hC : ∀ k<N,(crossGram
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep (dcSlideOneGradient fullMemory estimate) (A x) (g x) (k-1-i.val)))
      (fun i : Fin k => oneGradientStep (dcSlideOneGradient fullMemory estimate) (A x) (g x) (k-1-i.val))).det≠0)
    (ht : ∀ k<N,estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (A x) (g x) k)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate estimate k)
      (oneGradientData (dcSlideOneGradient fullMemory estimate) (A x) (g x) k)) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (dcSlideOneGradient fullMemory estimate) (A z) (g z) k) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (dcSlideOneGradient fullMemory estimate) (A z) (g z) i) x := by
  induction N with
  | zero =>
    refine ⟨?_,by intro i hi; omega⟩
    intro k hk
    have he : k=0 := by omega
    subst k
    exact hg
  | succ k ih =>
    obtain ⟨hG,hs⟩ := ih (fun i hi => hA i (by omega))
      (fun j hj => hC j (by omega)) (fun j hj => ht j (by omega)) (fun j hj => hT j (by omega))
    let m := dcSlideOneGradient fullMemory estimate
    let S := fun z (i : Fin k) => oneGradientStep m (A z) (g z) (k-1-i.val)
    let Y := fun z (i : Fin k) => A z (k-1-i.val) (S z i)
    let G := fun z => oneGradientGradient m (A z) (g z) k
    let a := fun z => estimate (oneGradientRun m (A z) (g z) k)
    have hS (i : Fin k) : ContDiffAt ℝ r (fun z => S z i) x := hs _ (by omega)
    have hY (i : Fin k) : ContDiffAt ℝ r (fun z => Y z i) x := (hA _ (by omega)).clm_apply (hS i)
    have ha := actual_trial_contDiffAt estimate m A g x k hg hs hG (hT k (by omega))
    have hd := contDiff_dataDeferredDirection S Y G a x hS hY (hG k le_rfl) ha (ht k (by omega)) (hC k (by omega))
    have hstep : ContDiffAt ℝ r (fun z => oneGradientStep m (A z) (g z) k) x := by
      apply (ha.smul hd).congr_of_eventuallyEq
      apply Filter.Eventually.of_forall
      intro z
      change a z • deferredDirection (windowSteps (selectedWindow fullMemory _))
        (windowImages (selectedWindow fullMemory _)) (G z) (a z)=_
      rw [oneGradient_full_deferred_coordinates]
      rfl
    have hnext : ContDiffAt ℝ r (fun z => oneGradientGradient m (A z) (g z) (k+1)) x := by
      simp only [oneGradientGradient_succ]
      exact (hG k le_rfl).add ((hA k (by omega)).clm_apply hstep)
    constructor
    · intro j hj
      by_cases he : j=k+1
      · subst j;exact hnext
      · exact hG j (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i;exact hstep
      · exact hs i (by omega)

/-- Genuine one-gradient DC quadratic references discharge every actual native
domain and therefore have C-r steps and gradients under primitive C-r estimates.
Use: the original full-memory cycle regularity is a consequence of the
implemented rule and positive true reference data, rather than a new premise.
Article: main_krylov, thm:dcs and lem:U(d).
Proof: derive the actual native determinant from the true execution flag,
then insert those domains and positive estimates into the genuine query induction. -/
theorem quadraticDC_one_gradient_contDiffAt {r : WithTop ℕ∞} (estimate : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N,0<estimate (oneGradientRun (dcSlideOneGradient fullMemory estimate) (fun _ => Q) (g x) i))
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate estimate k)
      (oneGradientData (dcSlideOneGradient fullMemory estimate) (A x) (g x) k)) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (dcSlideOneGradient fullMemory estimate) (A z) (g z) k) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (dcSlideOneGradient fullMemory estimate) (A z) (g z) i) x := by
  apply dc_one_gradient_prefix_contDiffAt estimate A g x N (fun i _ => hA i) hg _ _ hT
  · intro k hk
    rw [hAx]
    exact dc_one_gradient_array_domain estimate Q hQ hpos (g x) N hpre ht k hk.le
  · intro k hk
    rw [hAx]
    exact (ht k hk).ne'

end
end krylov.Cancellation

import krylov.Stability.VirtualRegularity
import krylov.Stability.TrialCoordinates
import krylov.Stability.XRFCModelDomains

/-!
Article: main_krylov, lem:U(d), actual C^r full-memory XRFC trajectory.
Use: derive actual finite execution regularity from primitive smooth trial
coefficients in the true finite observed-data charts and genuine inverse domains.
Source: real one-gradient induction, actual smooth virtual block solves and
proved quadratic XRFC basis positivity; C² trials need not be analytic.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every actually defined finite full-memory XRFC prefix is C^r under primitive C^r observed-data trial rules and C^r primitive operators and initial data.
Use: actual trajectory smoothness is proved by real query induction rather than assumed for the chosen trial sequence.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: the old true steps and returned gradients give a smooth actual finite
observation chart. Compose its primitive trial rule, solve the genuine smooth
virtual block, form the true queried displacement, and apply the real segment
operator to obtain the actual next gradient. -/
theorem xrfc_prefix_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (hM : ∀ k<N, (pairModel
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory trial) (A x) (g x) (k-1-i.val))
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep (xrfcMethod fullMemory trial) (A x) (g x) (k-1-i.val)))).det≠0)
    (hC : ∀ k<N, (crossGram
      (fun i : Fin k => A x (k-1-i.val) (oneGradientStep (xrfcMethod fullMemory trial) (A x) (g x) (k-1-i.val)))
      (fun i : Fin k => oneGradientStep (xrfcMethod fullMemory trial) (A x) (g x) (k-1-i.val))).det≠0)
    (hT : ∀ k<N, ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k)) :
    (∀ k≤N, ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcMethod fullMemory trial) (A z) (g z) k) x) ∧
      ∀ i<N, ContDiffAt ℝ r (fun z => oneGradientStep (xrfcMethod fullMemory trial) (A z) (g z) i) x := by
  -- The induction state retains every genuinely returned gradient needed by later primitive trial charts.
  induction N with
  | zero =>
    refine ⟨?_,by intro i hi; omega⟩
    intro k hk
    have he : k=0 := by omega
    subst k
    exact hg
  | succ k ih =>
    obtain ⟨hG,hs⟩ := ih (fun i hi => hA i (by omega))
      (fun j hj => hM j (by omega)) (fun j hj => hC j (by omega)) (fun j hj => hT j (by omega))
    have hV := oneGradient_virtualBlock_contDiffAt (xrfcMethod fullMemory trial) A g x k
      (fun i hi => hA i (by omega)) hs (hG k le_rfl) (hM k (by omega)) (hC k (by omega))
    have ht := actual_trial_contDiffAt trial (xrfcMethod fullMemory trial) A g x k hg hs hG (hT k (by omega))
    have hstep : ContDiffAt ℝ r (fun z => oneGradientStep (xrfcMethod fullMemory trial) (A z) (g z) k) x :=
      hV.1.add (ht.smul hV.2.2)
    have hnext : ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcMethod fullMemory trial) (A z) (g z) (k+1)) x := by
      simp only [oneGradientGradient_succ]
      exact (hG k le_rfl).add ((hA k (by omega)).clm_apply hstep)
    constructor
    · intro j hj
      by_cases he : j=k+1
      · subst j; exact hnext
      · exact hG j (by omega)
    · intro i hi
      by_cases he : i=k
      · subst i; exact hstep
      · exact hs i (by omega)

/-- Actual full-memory XRFC has genuine C^r gradients and evaluated steps near every nondegenerate positive quadratic reference with primitive C^r trial coefficients.
Use: r=2 discharges the source's XRFC trajectory-regularity assertion without analytic-trial assumptions or supplied inverse domains.
Article: main_krylov, lem:U(d), actual C² XRFC cycle map.
Proof: the true executed nonzero-trial quadratic basis theorem proves both
actual inverse domains at every reference prefix. Insert those genuine domains
and the primitive observed trial-chart hypotheses into the actual smooth
one-gradient execution induction. -/
theorem quadraticXRFC_prefix_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ k<N, ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k)) :
    (∀ k≤N, ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcMethod fullMemory trial) (A z) (g z) k) x) ∧
      ∀ i<N, ContDiffAt ℝ r (fun z => oneGradientStep (xrfcMethod fullMemory trial) (A z) (g z) i) x := by
  -- Both matrix domains are derived from the real reference execution before the smooth induction is invoked.
  apply xrfc_prefix_contDiffAt trial A g x N (fun i _ => hA i) hg _ _ hT
  · intro k hk
    rw [hAx]
    exact (xrfc_full_array_domains trial Q hQ hpos (g x) N hpre ht k hk.le).2
  · intro k hk
    rw [hAx]
    exact (xrfc_full_array_domains trial Q hQ hpos (g x) N hpre ht k hk.le).1

/-- Actual full-memory XRFC's unevaluated physical output and its semantic output gradient are C^r under primitive C^r trial coefficients at a genuine quadratic reference.
Use: r=2 covers the complete real output map, including the source's unevaluated terminal point and its actual output operator.
Article: main_krylov, lem:U(d), true XRFC cycle outputs.
Proof: real prefix smoothness gives every actual queried step and returned
gradient. The genuine terminal positive model supplies the final virtual solve.
Sum the actual physical queries, add the true unevaluated virtual correction,
and apply the real smooth output operator for the semantic output gradient. -/
theorem quadraticXRFC_output_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (B : X → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, ContDiffAt ℝ r (fun z => A z i) x) (hB : ContDiffAt ℝ r B x)
    (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N, trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ k<N, ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k)) :
    let m := xrfcMethod fullMemory trial (E := E)
    let H := fun z => oneGradientRun m (A z) (g z) N
    ContDiffAt ℝ r (fun z => m.outputDisplacement (H z)) x ∧
      ContDiffAt ℝ r (fun z => m.outputGradient (B z) (H z)) x := by
  -- The terminal output uses a real data-only solve; no additional gradient query is introduced.
  let m := xrfcMethod fullMemory trial (E := E)
  have htraj := quadraticXRFC_prefix_contDiffAt trial A g x hA hg Q hAx hQ hpos N hpre ht hT
  have hd := xrfc_full_array_domains trial Q hQ hpos (g x) N hpre ht N le_rfl
  have hv := oneGradient_virtualBlock_contDiffAt m A g x N (fun i _ => hA i)
    htraj.2 (htraj.1 N le_rfl) (by rw [hAx]; exact hd.2) (by rw [hAx]; exact hd.1)
  have hp : ContDiffAt ℝ r (fun z => (oneGradientRun m (A z) (g z) N).displacement) x := by
    simp only [oneGradientRun_displacement_sum]
    exact ContDiffAt.sum (fun i hi => htraj.2 i (Finset.mem_range.mp hi))
  exact ⟨hp.add hv.1,(htraj.1 N le_rfl).add (hB.clm_apply hv.1)⟩

end
end krylov.Stability

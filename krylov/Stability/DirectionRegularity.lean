import krylov.Methods.DirectionExecution
import krylov.Stability.ContDiffVirtual
import krylov.Stability.TrialCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, lem:U(d) and thm:I, primitive actual direction-replay regularity.
Use: derive full XRFC-D trajectory regularity by real query induction on the
actual reconstructed direction/image data and original observed trial charts.
Source: reused genuine finite virtual/conjugacy solve calculus and the real
one-gradient observation update, with no supplied trajectory regularity.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- True earlier replay observations give C-r actual XRFC-D virtual corrections,
virtual gradients and directions at the real two finite inverse domains.
Use: propagate primitive regularity through the original direction-basis policy.
Article: main_krylov, lem:U(d) and thm:I.
Proof: actual replay has its genuine fixed chronological arrays; compose the
existing smooth native finite solve and identify it with the actual implementation. -/
theorem xrfcD_virtualBlock_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (k : ℕ)
    (hd : ∀ i<k,ContDiffAt ℝ r (fun z => xrfcDExecutedDirection trial (A z) (g z) i) x)
    (hq : ∀ i<k,ContDiffAt ℝ r (fun z => xrfcDExecutedImage trial (A z) (g z) i) x)
    (hG : ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k) x)
    (hM : (pairModel
      (fun i : Fin k => xrfcDExecutedDirection trial (A x) (g x) (k-1-i.val))
      (fun i : Fin k => xrfcDExecutedImage trial (A x) (g x) (k-1-i.val))).det≠0)
    (hC : (crossGram
      (fun i : Fin k => xrfcDExecutedImage trial (A x) (g x) (k-1-i.val))
      (fun i : Fin k => xrfcDExecutedDirection trial (A x) (g x) (k-1-i.val))).det≠0) :
    ContDiffAt ℝ r (fun z => virtualCorrection (xrfcDWindow trial (A z) (g z) k)
      (oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k)) x ∧
      ContDiffAt ℝ r (fun z => xrfcDVirtualGradient trial (A z) (g z) k) x ∧
      ContDiffAt ℝ r (fun z => xrfcDExecutedDirection trial (A z) (g z) k) x := by
  let D := fun z (i : Fin k) => xrfcDExecutedDirection trial (A z) (g z) (k-1-i.val)
  let Q := fun z (i : Fin k) => xrfcDExecutedImage trial (A z) (g z) (k-1-i.val)
  let G := fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k
  have hD (i : Fin k) : ContDiffAt ℝ r (fun z => D z i) x := hd _ (by omega)
  have hQ (i : Fin k) : ContDiffAt ℝ r (fun z => Q z i) x := hq _ (by omega)
  have h := contDiff_virtualBlock D Q G x hD hQ hG hM hC
  have hcorr := h.1.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun z => (xrfcD_virtual_coordinates trial (A z) (g z) k).1))
  have hgrad := h.2.1.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun z => (xrfcD_virtual_coordinates trial (A z) (g z) k).2))
  refine ⟨hcorr,hgrad,?_⟩
  apply (contDiff_conjugacyDirection D Q _ x hD hQ hgrad hC).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun z => xrfcD_direction_coordinates trial (A z) (g z) k)

/-- Every genuinely defined finite original XRFC-D trajectory is C-r from
primitive C-r operator paths and actual observed-data trial charts.
Use: replay smoothness is derived simultaneously with the real queried steps
and returned gradients, including inverse-trial image reconstruction.
Article: main_krylov, lem:U(d) and thm:I.
Proof: real query induction retains all earlier actual steps, directions,
images and observations. The true native virtual block and primitive trial
composition give the next actual query; its returned gradient defines the
new genuine replay image through the nonzero actual trial. -/
theorem xrfcD_prefix_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ)
    (hA : ∀ i<N,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (hM : ∀ k<N,(pairModel
      (fun i : Fin k => xrfcDExecutedDirection trial (A x) (g x) (k-1-i.val))
      (fun i : Fin k => xrfcDExecutedImage trial (A x) (g x) (k-1-i.val))).det≠0)
    (hC : ∀ k<N,(crossGram
      (fun i : Fin k => xrfcDExecutedImage trial (A x) (g x) (k-1-i.val))
      (fun i : Fin k => xrfcDExecutedDirection trial (A x) (g x) (k-1-i.val))).det≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (A x) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (A x) (g x) k)) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k) x) ∧
      (∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (xrfcDMethod fullMemory trial) (A z) (g z) i) x) ∧
      (∀ i<N,ContDiffAt ℝ r (fun z => xrfcDExecutedDirection trial (A z) (g z) i) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => xrfcDExecutedImage trial (A z) (g z) i) x := by
  induction N with
  | zero =>
    refine ⟨?_,by intro i hi;omega,by intro i hi;omega,by intro i hi;omega⟩
    intro k hk
    have he : k=0 := by omega
    subst k
    exact hg
  | succ k ih =>
    obtain ⟨hG,hs,hd,hq⟩ := ih (fun i hi => hA i (by omega))
      (fun j hj => hM j (by omega)) (fun j hj => hC j (by omega))
      (fun j hj => ht j (by omega)) (fun j hj => hT j (by omega))
    have hv := xrfcD_virtualBlock_contDiffAt trial A g x k hd hq (hG k le_rfl)
      (hM k (by omega)) (hC k (by omega))
    have htau := actual_trial_contDiffAt trial (xrfcDMethod fullMemory trial) A g x k hg hs hG (hT k (by omega))
    have hstep : ContDiffAt ℝ r (fun z => oneGradientStep (xrfcDMethod fullMemory trial) (A z) (g z) k) x :=
      hv.1.add (htau.smul hv.2.2)
    have hnext : ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) (k+1)) x := by
      simp only [oneGradientGradient_succ]
      exact (hG k le_rfl).add ((hA k (by omega)).clm_apply hstep)
    have hqnext : ContDiffAt ℝ r (fun z => xrfcDExecutedImage trial (A z) (g z) k) x :=
      (htau.inv (ht k (by omega))).smul (hnext.sub hv.2.1)
    refine ⟨?_,?_,?_,?_⟩
    · intro j hj
      by_cases he : j=k+1
      · subst j;exact hnext
      · exact hG j (by omega)
    · intro j hj
      by_cases he : j=k
      · subst j;exact hstep
      · exact hs j (by omega)
    · intro j hj
      by_cases he : j=k
      · subst j;exact hv.2.2
      · exact hd j (by omega)
    · intro j hj
      by_cases he : j=k
      · subst j;exact hqnext
      · exact hq j (by omega)

end
end krylov.Stability

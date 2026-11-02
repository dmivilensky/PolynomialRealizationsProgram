import krylov.Stability.DirectionRegularity
import krylov.Methods.DirectionReference
set_option autoImplicit false
/-!
Article: main_krylov, lem:U(d) and thm:I, complete primitive XRFC-D C-r calculus.
Use: derive the actual varying-prefix direction-basis trajectory and native
unevaluated output regularity from original trial charts and genuine quadratic
reference data; no smooth trajectory or inverse-domain field is assumed.
Source: real direction-replay query induction and the reused actual positive
quadratic reference domains, including the terminal native solve.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original full-memory direction-basis XRFC prefix has genuine C-r
returned gradients, real evaluated steps, directions and observed replay images
near every actual nondegenerate positive quadratic reference.
Use: r=2 supplies the source's direction-basis primitive trajectory calculus.
Article: main_krylov, lem:U(d) and thm:I.
Proof: all actual reference inverse domains are derived from quadratic replay
correctness and true positive CG geometry; the real query induction then
propagates precisely the primitive trial-chart and operator regularity. -/
theorem quadraticXRFCD_prefix_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (A x) (g x) k)) :
    (∀ k≤N,ContDiffAt ℝ r (fun z => oneGradientGradient (xrfcDMethod fullMemory trial) (A z) (g z) k) x) ∧
      (∀ i<N,ContDiffAt ℝ r (fun z => oneGradientStep (xrfcDMethod fullMemory trial) (A z) (g z) i) x) ∧
      (∀ i<N,ContDiffAt ℝ r (fun z => xrfcDExecutedDirection trial (A z) (g z) i) x) ∧
      ∀ i<N,ContDiffAt ℝ r (fun z => xrfcDExecutedImage trial (A z) (g z) i) x := by
  apply xrfcD_prefix_contDiffAt trial A g x N (fun i _ => hA i) hg _ _ _ hT
  · intro k hk
    rw [hAx]
    exact (xrfcD_full_array_domains trial Q hQ hpos (g x) N hpre ht k hk.le).2
  · intro k hk
    rw [hAx]
    exact (xrfcD_full_array_domains trial Q hQ hpos (g x) N hpre ht k hk.le).1
  · rw [hAx]
    exact ht

/-- The actual original direction-basis XRFC unevaluated point and its true
semantic output gradient are C-r under primitive C-r observed trial rules.
Use: the source quadratic Taylor remainder follows for the genuine native
output without observing an additional gradient at that virtual point.
Article: main_krylov, lem:U(d) and thm:I.
Proof: actual query regularity supplies all true replay vectors and returned
gradients. The genuine terminal reference domain makes the native output
correction smooth; sum the real queried steps and apply the actual output
operator for the semantic gradient. -/
theorem quadraticXRFCD_output_contDiffAt {r : WithTop ℕ∞} (trial : History E → ℝ)
    (A : X → ℕ → E →L[ℝ] E) (B : X → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i,ContDiffAt ℝ r (fun z => A z i) x) (hB : ContDiffAt ℝ r B x)
    (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q (g x) i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ r (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (A x) (g x) k)) :
    let m := xrfcDMethod fullMemory trial (E := E)
    let H := fun z => oneGradientRun m (A z) (g z) N
    ContDiffAt ℝ r (fun z => m.outputDisplacement (H z)) x ∧
      ContDiffAt ℝ r (fun z => m.outputGradient (B z) (H z)) x := by
  let m := xrfcDMethod fullMemory trial (E := E)
  have hreg := quadraticXRFCD_prefix_contDiffAt trial A g x hA hg Q hAx hQ hpos N hpre ht hT
  have hdom := xrfcD_full_array_domains trial Q hQ hpos (g x) N hpre ht N le_rfl
  have hv := xrfcD_virtualBlock_contDiffAt trial A g x N hreg.2.2.1 hreg.2.2.2 (hreg.1 N le_rfl)
    (by rw [hAx];exact hdom.2) (by rw [hAx];exact hdom.1)
  have hp : ContDiffAt ℝ r (fun z => (oneGradientRun m (A z) (g z) N).displacement) x := by
    simp only [oneGradientRun_displacement_sum]
    exact ContDiffAt.sum (fun i hi => hreg.2.1 i (Finset.mem_range.mp hi))
  exact ⟨hp.add hv.1,(hreg.1 N le_rfl).add (hB.clm_apply hv.1)⟩

end
end krylov.Stability

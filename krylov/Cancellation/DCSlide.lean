import krylov.Methods.DeferredReference
import krylov.Methods.DeferredActualResidual
import krylov.Methods.OneGradientCoordinates
import krylov.Methods.InformationSpan
set_option autoImplicit false
/-!
Article: main_krylov, s8:dcsdef, s3:def:DC and thm:dcs(a,b,c).
Use: implement sliding and deferred cancellation with genuine data-dependent
estimates, and derive the exact old-residual recursion on the actual runs.
Source: the observed tilted conjugacy solve and the actual secant identity;
quadratic consistency reuses the proved FC transcript and CG orthogonality.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The data-only tilted direction with its actual retained observed window.
Use: both DC-slide information classes use the same observed conjugacy solve.
Article: main_krylov, s8:dcsdef.
Proof: insert the current observed estimate into the previously proved solve. -/
def dcSlideDirection (memory : ℕ → ℕ) (estimate : History E → ℝ) (H : History E) : E :=
  deferredDirection (windowSteps (selectedWindow memory H))
    (windowImages (selectedWindow memory H)) H.gradient (estimate H)

/-- DC-slide with an actual exact search and no correction evaluations.
Use: the unknown operators are absent from the direction and estimate policies.
Article: main_krylov, s8:dcsdef, class (M).
Proof: every iteration executes the data-only tilted direction with an empty
correction tree. -/
def dcSlideMethod (memory : ℕ → ℕ) (estimate : History E → ℝ) : ProbedMethod E where
  direction := dcSlideDirection memory estimate
  correction _ _ := .done

/-- One-gradient DC-slide chooses the estimate before evaluating the new gradient.
Use: this is the actual nonanticipating one-gradient cancellation executor.
Article: main_krylov, s8:dcsdef, class (1g).
Proof: the chosen displacement is the data-only estimate times the tilted
direction; the final point requires no additional displacement. -/
def dcSlideOneGradient (memory : ℕ → ℕ) (estimate : History E → ℝ) : OneGradientMethod E where
  step H := estimate H • dcSlideDirection memory estimate H
  output _ := 0

/-- Deferred cancellation permits a genuinely data-dependent final estimate.
Use: close the source's policy definition beyond constant final estimates.
Article: main_krylov, s3:def:DC.
Proof: execute FC until the prescribed final iteration and then use the same
data-only tilted solve as DC-slide. -/
def deferredDataMethod (memory : ℕ → ℕ) (N : ℕ) (estimate : History E → ℝ) : ProbedMethod E where
  direction H := if H.records.length+1=N then dcSlideDirection memory estimate H
    else (fcMethod memory).direction H
  correction _ _ := .done

/-- A constant final estimate recovers the already implemented deferred method.
Use: all earlier actual deferred-source theorems remain available verbatim.
Article: main_krylov, s3:def:DC.
Proof: the two actual decision functions coincide. -/
theorem deferred_data_constant (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) :
    deferredDataMethod memory N (fun _ : History E => a)=deferredMethod memory N a := rfl

/-- DC-slide has an empty actual correction tree at every history.
Use: its recorded secants are exactly the true line-operator images.
Article: main_krylov, s8:dcsdef.
Proof: read the concrete correction field. -/
theorem dc_slide_correction_free (memory : ℕ → ℕ) (estimate : History E → ℝ) :
    CorrectionFree (dcSlideMethod memory estimate) := fun _ _ => rfl

/-- The actual DC-slide direction belongs to the observed information span.
Use: admissibility is proved for every history, independently of any trajectory.
Article: main_krylov, s8:dcsdef.
Proof: the direction combines the observed current gradient and retained steps. -/
theorem dc_slide_direction_observed (memory : ℕ → ℕ) (estimate : History E → ℝ) (H : History E) :
    dcSlideDirection memory estimate H∈H.observedSpan :=
  H.observedSpan.add_mem (H.observedSpan.neg_mem H.gradient_mem_observedSpan)
    (combine_mem _ _ (windowSteps_mem_observedSpan memory H) _)

/-- Exact-search DC-slide obeys the source's actual information restrictions.
Use: it is an admissible probed method with no correction query.
Article: main_krylov, s8:dcsdef.
Proof: combine the observed direction with the empty correction tree. -/
theorem dc_slide_span_restricted (memory : ℕ → ℕ) (estimate : History E → ℝ) :
    ProbedSpanRestricted memory (dcSlideMethod memory estimate) :=
  fun H => ⟨dc_slide_direction_observed memory estimate H,fun _ => trivial⟩

/-- One-gradient DC-slide obeys the actual evaluated-step information restriction.
Use: its estimate is read before any new gradient or curvature is available.
Article: main_krylov, s8:dcsdef.
Proof: scale the proved observed-span direction by its data-only estimate. -/
theorem dc_slide_one_gradient_span_restricted (memory : ℕ → ℕ) (estimate : History E → ℝ) :
    OneGradientSpanRestricted (dcSlideOneGradient memory estimate) :=
  fun H => H.observedSpan.smul_mem _ (dc_slide_direction_observed memory estimate H)

/-- Deferred cancellation with a data-dependent estimate is also source admissible.
Use: no regularity or quadratic consistency assumption replaces nonanticipation.
Article: main_krylov, s3:def:DC.
Proof: both actually selected direction branches lie in the observed span. -/
theorem deferred_data_span_restricted (memory : ℕ → ℕ) (N : ℕ) (estimate : History E → ℝ) :
    ProbedSpanRestricted memory (deferredDataMethod memory N estimate) := by
  intro H
  refine ⟨?_,fun _ => trivial⟩
  change (if H.records.length+1=N then _ else _)∈H.observedSpan
  split
  · exact dc_slide_direction_observed memory estimate H
  · exact retained_direction_mem_observedSpan memory H

/-- On a true quadratic reference transcript, the data-dependent tilt vanishes.
Use: consistency follows from real CG orthogonality, without constraining the estimate.
Article: main_krylov, thm:dcs(b).
Proof: every actual retained-step residual is zero, so the observed tilted solve
equals FC even on its totalized solved tail. -/
theorem dc_slide_reference_direction (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hp : H.pairs=referencePairs Q g k) (hg : H.gradient=CG.gradient Q g k) :
    dcSlideDirection memory estimate H=(fcMethod memory).direction H := by
  exact deferredDirection_eq_conjugacy _ _ _ _
    (history_reference_coordinates_zero Q hQ hpos g k H hp hg memory)

/-- The entire quadratic DC-slide history equals the actual FC history.
Use: all actual gradients, secants and physical iterates have the CG reference.
Article: main_krylov, thm:dcs(b), exact searches.
Proof: induct on real histories; the proved reference residuals remove the
tilt before executing each actual search. -/
theorem dc_slide_reference_run (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k=
      methodRun (fcMethod memory) (fun _ => Q) (fun _ => Q) g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih]
    have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
    have hd := dc_slide_reference_direction memory estimate Q hQ hpos g k _ hs.2 hs.1
    unfold methodAdvance
    change _= _
    rw [show (dcSlideMethod memory estimate).direction _=(fcMethod memory).direction _ from hd]
    rfl

/-- Exact-search DC-slide is globally CG-consistent for every positive memory.
Use: the consistency claim includes all actual solved tails and arbitrary
data-dependent estimates.
Article: main_krylov, thm:dcs(b).
Proof: transfer the real FC consistency witness through complete history equality
and the proved vanishing reference tilt. -/
theorem dc_slide_consistent (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) : CGConsistent (dcSlideMethod memory estimate) := by
  intro Q hQ hpos g k
  have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
  obtain ⟨c,hc,hd,_⟩ := fcMethod_consistent memory hm Q hQ hpos g k
  refine ⟨c,hc,?_,by trivial⟩
  rw [dc_slide_reference_run memory hm estimate Q hQ hpos g k]
  change dcSlideDirection memory estimate _=_
  rw [dc_slide_reference_direction memory estimate Q hQ hpos g k _ hs.2 hs.1]
  exact hd

/-- The exact scalar residual identity behind both actually executed variants.
Use: preserve the genuine finite operator defect without a first-order approximation.
Article: main_krylov, thm:dcs(a).
Proof: symmetry transfers the old secant action to the new direction; the
observed tilted pairing supplies the residual multiplier. -/
theorem tilted_residual_identity (A C : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (s g d : E) (a t : ℝ) (hp : inner ℝ (A s) d= -a⁻¹*inner ℝ s g) :
    inner ℝ s (g+t • C d)=
      (1-t/a)*inner ℝ s g+inner ℝ s ((C-A) (t • d)) := by
  have hs := hA s d
  change inner ℝ (A s) d=inner ℝ s (A d) at hs
  rw [hs] at hp
  simp only [inner_add_right,real_inner_smul_right,_root_.sub_apply,map_smul,inner_sub_right,hp]
  ring

/-- Every retained actual old step satisfies the exact DC-slide residual recursion.
Use: this is the article's finite-variation identity on the real exact-search run.
Article: main_krylov, thm:dcs(a).
Proof: locate the actual retained pair, read its genuine nonsingular observed
tilted solve, and substitute the real correction-free secant, search and step. -/
theorem dc_slide_residual (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hmem : (probedStep (dcSlideMethod memory estimate) A B g i,
      probedSecant (dcSlideMethod memory estimate) A B g i)∈
      selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g k))
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g k)))
      (windowSteps (selectedWindow memory (methodRun (dcSlideMethod memory estimate) A B g k)))).det) :
    let m := dcSlideMethod memory estimate
    let H := methodRun m A B g k
    let t := lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)
    inner ℝ (probedStep m A B g i) (probedGradient m A B g (k+1))=
      (1-t/estimate H)*inner ℝ (probedStep m A B g i) (probedGradient m A B g k)+
        inner ℝ (probedStep m A B g i) ((A k-A i) (probedStep m A B g k)) := by
  let m := dcSlideMethod memory estimate
  let H := methodRun m A B g k
  let W := selectedWindow memory H
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hmem
  have hx : windowSteps W ⟨j,hj⟩=probedStep m A B g i := congrArg Prod.fst hget
  have hy : windowImages W ⟨j,hj⟩=probedSecant m A B g i := congrArg Prod.snd hget
  have hp := deferredDirection_conjugacy (windowSteps W) (windowImages W)
    H.gradient (estimate H) hdet ⟨j,hj⟩
  change inner ℝ (windowImages W ⟨j,hj⟩) (probedDirection m A B g k)=_ at hp
  rw [hx,hy,correctionFree_secant m (dc_slide_correction_free memory estimate)] at hp
  dsimp only
  rw [correctionFree_gradient_succ m (dc_slide_correction_free memory estimate) A B g k,
    correctionFree_step m (dc_slide_correction_free memory estimate) A B g k]
  exact tilted_residual_identity (A i) (A k) hAi _ _ _ _ _ hp

/-- One-gradient DC-slide cancels every retained old residual exactly.
Use: at finite variation only the fresh segment defect survives; no asymptotic
remainder or quadratic consistency is assumed.
Article: main_krylov, thm:dcs(c), one-gradient variant.
Proof: read the actual retained tilted equation, then use the very same nonzero
estimate as the executed step length in the exact residual identity. -/
theorem dc_slide_one_gradient_fresh (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (A : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hmem : (oneGradientStep (dcSlideOneGradient memory estimate) A g i,
      A i (oneGradientStep (dcSlideOneGradient memory estimate) A g i))∈
      selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate) A g k))
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate) A g k)))
      (windowSteps (selectedWindow memory (oneGradientRun (dcSlideOneGradient memory estimate) A g k)))).det)
    (ha : estimate (oneGradientRun (dcSlideOneGradient memory estimate) A g k)≠0) :
    let m := dcSlideOneGradient memory estimate
    inner ℝ (oneGradientStep m A g i) (oneGradientGradient m A g (k+1))=
      inner ℝ (oneGradientStep m A g i) ((A k-A i) (oneGradientStep m A g k)) := by
  let m := dcSlideOneGradient memory estimate
  let H := oneGradientRun m A g k
  let W := selectedWindow memory H
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hmem
  have hx : windowSteps W ⟨j,hj⟩=oneGradientStep m A g i := congrArg Prod.fst hget
  have hy : windowImages W ⟨j,hj⟩=A i (oneGradientStep m A g i) := congrArg Prod.snd hget
  have hp := deferredDirection_conjugacy (windowSteps W) (windowImages W)
    H.gradient (estimate H) hdet ⟨j,hj⟩
  rw [hx,hy] at hp
  have he := tilted_residual_identity (A i) (A k) hAi _ _ _ (estimate H) (estimate H) hp
  rw [div_self ha,sub_self,zero_mul,zero_add] at he
  dsimp only
  rw [oneGradientGradient_succ]
  change inner ℝ (oneGradientStep m A g i)
    (H.gradient+A k (estimate H • deferredDirection (windowSteps W) (windowImages W) H.gradient (estimate H)))=
      inner ℝ (oneGradientStep m A g i)
        ((A k-A i) (estimate H • deferredDirection (windowSteps W) (windowImages W) H.gradient (estimate H)))
  rw [map_smul]
  exact he

end
end krylov.Cancellation

import krylov.Cancellation.DeferredDataExecution
import krylov.Cancellation.DeferredDataSmooth
import krylov.Cancellation.DCEstimateRegularity
import krylov.Envelope.DeferredModelDomain
import krylov.Envelope.ZeroOperatorPairJet
import krylov.Envelope.FCResidualVariation
import krylov.Variation.FCResponse
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original arbitrary observed-estimate residual first jets.
Use: derive the genuine final residual derivative for a positive C-two
observed final estimate, retaining its actual uncalibrated reference value.
Source: real data-dependent deferred prefix and exact last residual transfer,
primitive native C-two compilation, actual FC residual staircase derivative
and the genuine zero-reference physical segment-difference product calculus.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Stability krylov.Variation krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- Every actual old-step residual first derivative of original data-dependent
DC is its true fresh physical defect plus the original reference damping
factor times the real pre-final FC staircase response.
Use: the derivative of the arbitrary observed final estimate cancels because
the actual old residual is zero at the genuine quadratic reference.
Article: main_krylov, thm:DC, full uncalibrated original residual coordinates.
Proof: primitive C-two estimate charts derive actual fields, search and chosen
estimate regularity. The entire pre-final history is exactly FC, so the actual
old residual has its proved true FC staircase derivative. Its zero reference
value removes the estimate derivative in the real damping product. A genuine
zero-reference segment difference removes both moving-step derivatives in the
fresh term. Differentiate the original exact native residual identity on its
proved actual retained inverse neighborhood. -/
theorem deferred_data_residual_derivative
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ j<k+1,ContDiffAt ℝ 2 (fun t => B t j) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : k+1≤referenceAtomCount base hb g)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) (i : ℕ) (hi : i<k) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    let A := canonicalFCPath base E
    deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i) (probedGradient m (A t) (B t) g (k+1))) 0=
      (1-CG.length Q g k/a0)*
        (∑ j∈Finset.Ico (i+1) k,inner ℝ (referenceStep Q g i)
          ((cumulativeDrift base E j-cumulativeDrift base E i) (referenceStep Q g j)))+
      inner ℝ (referenceStep Q g i)
        ((cumulativeDrift base E k-cumulativeDrift base E i) (referenceStep Q g k)) := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let A := canonicalFCPath base E
  let H := fun t => methodRun m (A t) (B t) g k
  let S := fun j t => probedStep m (A t) (B t) g j
  let G := fun j t => probedGradient m (A t) (B t) g j
  let a := fun t => estimate (H t)
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let alpha := fun t => lineLength (G k t) (probedDirection m (A t) (B t) g k) (probedProbe m (A t) (B t) g k)
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hcount)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hA0 : A 0=fun _ => Q := canonicalFCPath_zero base E
  have hsmooth := deferred_data_smoothCycleAt fullMemory (fun _ hj => hj) (k+1) estimate Q hQ hpos g (k+1)
    hpre 2 (fun j _ hj => by
      have he : j=k := by omega
      subst j
      exact ha)
    (fun j _ hj => by
      have he : j=k := by omega
      subst j
      exact ha0)
  have hconsistent := deferred_data_consistent fullMemory (fun _ hj => hj) (k+1) estimate (E := EuclideanSpace ℝ (Fin n))
  have hfields (j : ℕ) (hj : j<k+1) := smoothProbed_fields_regular m hconsistent A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth j hj
  have hSi : ContDiffAt ℝ 2 (S i) 0 := (hfields i (by omega)).2.2.1
  have hSk : ContDiffAt ℝ 2 (S k) 0 := (hfields k (by omega)).2.2.1
  have hGk : ContDiffAt ℝ 2 (G k) 0 := smoothProbed_gradient_regular m hconsistent A B (fun _ => g) 0 k
    (fun j _ => hA j) (fun j hj => hB j (by omega)) contDiffAt_const Q hA0 hB0 hQ hpos
    (fun j hj => hpre j (by omega)) (hsmooth.mono m (by omega))
  have halpha : ContDiffAt ℝ 2 alpha 0 := (smoothProbed_search_regular m hconsistent A B (fun _ => g) 0 (k+1)
    (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ hpos hpre hsmooth k (by omega)).1
  have htrace := smoothProbed_trace_regular m hconsistent A B (fun _ => g) 0 k
    (fun j _ => hA j) (fun j hj => hB j (by omega)) contDiffAt_const Q hA0 hB0 hQ hpos
    (fun j hj => hpre j (by omega)) (hsmooth.mono m (by omega))
  have haF : ContDiffAt ℝ 2 a 0 := by
    apply actual_history_estimate_contDiffAt estimate H 0 htrace
    · exact Eventually.of_forall fun t =>
        (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A t) (B t) g k).trans
          (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A 0) (B 0) g k).symm
    · have he : H 0=methodRun m (fun _ => Q) (fun _ => Q) g k := by dsimp only [H];rw [hA0,hB0]
      rw [he]
      exact ha
  have haF0 : a 0=a0 := by dsimp only [a,H,a0];rw [hA0,hB0]
  have haNZ : a 0≠0 := haF0 ▸ ha0.ne'
  have hS0 (j : ℕ) : S j 0=referenceStep Q g j := by
    dsimp only [S]
    rw [hA0,hB0]
    exact quadratic_probedStep_eq_cg m hconsistent Q hQ hpos g j
  have hG0 : G k 0=CG.gradient Q g k := by
    dsimp only [G]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg m hconsistent Q hQ hpos g k
  have hd0 : probedDirection m (A 0) (B 0) g k=CG.direction Q g k := by
    rw [hA0,hB0]
    exact deferred_data_quadratic_direction fullMemory (fun _ hj => hj) (k+1) estimate Q hQ hpos g k
  have hz0 : probedProbe m (A 0) (B 0) g k=Q (CG.direction Q g k) := by
    dsimp only [probedProbe]
    rw [hd0,hA0]
  have halpha0 : alpha 0=CG.length Q g k := by dsimp only [alpha];rw [hG0,hd0,hz0]
  have hR0 : inner ℝ (S i 0) (G k 0)=0 := by
    rw [hS0 i,hG0,referenceStep,real_inner_smul_left,(CG.invariant Q hQ hpos g k
      (fun j hj => hpre j (by omega))).old_direction i hi,mul_zero]
  have hFCeq : (fun t => inner ℝ (S i t) (G k t))=
      fun t => inner ℝ (fcStep fullMemory (A t) g i) (fcGradient fullMemory (A t) g k) := by
    funext t
    change inner ℝ (probedStep m (A t) (B t) g i) (methodRun m (A t) (B t) g k).gradient=_
    rw [deferred_data_step_before fullMemory (k+1) estimate (A t) (B t) g i (by omega),
      deferred_data_run_before fullMemory (k+1) estimate (A t) (B t) g k (by omega)]
    have hf := correctionFree_run_independent (fcMethod fullMemory) (Variation.fcMethod_correctionFree fullMemory) (A t) (B t) (A t) g
    have hstep := congrArg (fun V : History (EuclideanSpace ℝ (Fin n)) => V.observationList.getD 4 0) (hf (i+1))
    change probedStep (fcMethod fullMemory) (A t) (B t) g i=probedStep (fcMethod fullMemory) (A t) (A t) g i at hstep
    rw [hstep,hf k,correctionFree_step _ (Variation.fcMethod_correctionFree fullMemory)]
    rfl
  have hRderiv := fullFC_residual_firstVariation A (cumulativeDrift base E) g
    (fun j => (canonicalFCPath_calculus base E j).1) (fun j => (canonicalFCPath_calculus base E j).2)
    (canonicalFCPath_symmetric base hb E hE) Q hA0 hQ hpos k (fun j hj => hpre j (by omega)) hi
  rw [← hFCeq] at hRderiv
  have hepsilon : ContDiffAt ℝ 2 (fun t : ℝ => 1-alpha t/a t) 0 := contDiffAt_const.sub (halpha.div haF haNZ)
  have hproduct := (hepsilon.differentiableAt (by norm_num)).hasDerivAt.fun_mul
    ((hSi.inner ℝ hGk).differentiableAt (by norm_num)).hasDerivAt
  simp only [haF0,halpha0,hR0,mul_zero,zero_add,hRderiv] at hproduct
  have hD := zero_operator_pair_hasDeriv (S i) (S k) (fun t => A t k-A t i)
    (deriv (S i) 0) (deriv (S k) 0) (cumulativeDrift base E k-cumulativeDrift base E i)
    (hSi.differentiableAt (by norm_num)).hasDerivAt (hSk.differentiableAt (by norm_num)).hasDerivAt
    ((canonicalFCPath_calculus base E k).2.sub (canonicalFCPath_calculus base E i).2)
    (by rw [hA0,sub_self])
  rw [hS0 i,hS0 k] at hD
  have hdom := deferred_last_model_domain A B g k 1 (fun j => (canonicalFCPath_calculus base E j).1) Q hA0 hQ hpos hpre
  have heq : (fun t => inner ℝ (S i t) (G (k+1) t))=ᶠ[𝓝 (0 : ℝ)]
      fun t => (1-alpha t/a t)*inner ℝ (S i t) (G k t)+inner ℝ (S i t) ((A t k-A t i) (S k t)) := by
    filter_upwards [hdom] with t ht
    have hprefixEq : methodRun m (A t) (B t) g k=
        methodRun (deferredMethod fullMemory (k+1) 1) (A t) (B t) g k :=
      (deferred_data_run_before fullMemory (k+1) estimate (A t) (B t) g k (by omega)).trans
        (deferredMethod_run_before fullMemory (k+1) 1 (A t) (B t) g k (by omega)).symm
    have hnewdom : IsUnit (crossGram (windowImages (selectedWindow fullMemory (H t)))
        (windowSteps (selectedWindow fullMemory (H t)))).det := by
      change IsUnit (crossGram (windowImages (selectedWindow fullMemory (methodRun m (A t) (B t) g k)))
        (windowSteps (selectedWindow fullMemory (methodRun m (A t) (B t) g k)))).det
      rw [hprefixEq]
      exact ht
    exact deferred_data_last_residual estimate (A t) (B t) g k i hi (canonicalFCPath_symmetric base hb E hE t i) hnewdom
  exact ((hproduct.add hD).congr_of_eventuallyEq heq).deriv

end
end krylov.Cancellation

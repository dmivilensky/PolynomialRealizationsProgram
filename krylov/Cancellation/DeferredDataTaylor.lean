import krylov.Cancellation.DeferredDataFirstVariation
import krylov.Stability.FirstOrderTaylor
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original actual deferred expansion with quadratic remainder.
Use: turn the proved genuine full-cycle observed-estimate first jet into the
literal original canonical source expansion with a derived O(t squared) bound.
Source: primitive native C-two observed execution, actual zero terminal CG
reference and the existing real C-two first-order Taylor remainder theorem.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
variable {n : ℕ}

/-- The original canonical perturbation source gives the actual full native
DC gradient expansion with its literal deferred spatial response and a genuine
quadratic remainder for every positive C-two observed final estimate.
Use: the first-order response and the actual remainder are both derived from
the real original executor; no smooth response or remainder field is supplied.
Article: main_krylov, thm:DC, actual full-cycle canonical source expansion.
Proof: the original primitive final estimate chart gives native C-two returned
gradient regularity. Its genuine full quadratic reference gradient is zero.
The proved actual first jet identifies the printed original deferred response;
the existing true C-two vector Taylor theorem supplies the quadratic bound. -/
theorem deferred_data_canonical_expansion
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hB : ∀ j<k+1,ContDiffAt ℝ 2 (fun t => B t j) 0) (hB0 : B 0=fun _ => cgOperator base)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha :
      let H := methodRun (deferredDataMethod fullMemory (k+1) estimate)
        (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : 0<estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k)) :
    let Q := cgOperator base
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let m := deferredDataMethod fullMemory (k+1) estimate
    let A := canonicalFCPath base E
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖R (probedGradient m (A t) (B t) g (k+1))-
        t • deferredResponse base g k (1-CG.length Q g k/a0) E‖≤C*t^2 := by
  let Q := cgOperator base
  let m := deferredDataMethod fullMemory (k+1) estimate
  let A := canonicalFCPath base E
  let a0 := estimate (methodRun m (fun _ => Q) (fun _ => Q) g k)
  let epsilon := 1-CG.length Q g k/a0
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let Phi := fun t => R (probedGradient m (A t) (B t) g (k+1))
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hN : k+1≤referenceAtomCount base hb g := by omega
  have hpre (j : ℕ) (hj : j<k+1) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_le hN)
  have hA (j : ℕ) : ContDiffAt ℝ 2 (fun t => A t j) 0 := (canonicalFCPath_calculus base E j).1.contDiffAt
  have hA0 : A 0=fun _ => Q := canonicalFCPath_zero base E
  have hG : ContDiffAt ℝ 2 (fun t => probedGradient m (A t) (B t) g (k+1)) 0 :=
    deferred_data_gradient_contDiffAt fullMemory (fun _ hj => hj) (k+1) estimate A B (fun _ => g) 0 (k+1)
      (fun j _ => hA j) hB contDiffAt_const Q hA0 hB0 hQ hpos hpre
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha)
      (fun j _ hj => by
        have he : j=k := by omega
        subst j
        exact ha0)
  have hPhi : ContDiffAt ℝ 2 Phi 0 := R.contDiff.contDiffAt.comp 0 hG
  have hderiv := deferred_data_full_hasDerivAt estimate base hb g E hE B k hB hB0 hcount hfull ha ha0
  have hPhi0 : Phi 0=0 := by
    change R (probedGradient m (A 0) (B 0) g (k+1))=0
    rw [hA0,hB0]
    change R (probedGradient m (fun _ => Q) (fun _ => Q) g (k+1))=0
    have hg0 : probedGradient m (fun _ => Q) (fun _ => Q) g (k+1)=CG.gradient Q g (k+1) :=
      quadratic_gradient_eq_cg m (deferred_data_consistent fullMemory (fun _ hj => hj) (k+1) estimate) Q hQ hpos g (k+1)
    rw [hg0]
    have hstop : CG.gradient Q g (k+1)=0 := (cg_stopping_iff base hb g (k+1)).mpr (by omega)
    rw [hstop,map_zero]
  obtain ⟨delta,C,hd,hC,hbound⟩ := c2_first_order_remainder Phi (deferredResponse base g k epsilon E) hPhi hderiv
  refine ⟨delta,C,hd,hC,?_⟩
  intro t ht
  simpa only [hPhi0,sub_zero] using hbound t ht

end
end krylov.Cancellation

import krylov.Cancellation.DCReferenceDamping
import krylov.Cancellation.DeferredFullProfile
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original observed arithmetic DC coefficient improvement.
Use: derive the true deferred reference damping bound for the implemented
single observed Gauss--Radau policy and its sharp comparison with actual FC.
Source: genuine complete quadratic history dictionaries, native true CG
searches, proved actual arithmetic spectral damping and original sharp tail comparisons.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The actual exact-search sliding DC reference direction is the original
unscaled CG direction for every observed estimate and every positive memory.
Use: identify the real searched length in the original reference damping factor.
Article: main_krylov, thm:DC and thm:dcs.
Proof: actual complete quadratic histories equal FC; the true zero old
residual removes the tilt and native retained conjugacy uniqueness gives CG. -/
theorem dc_slide_quadratic_direction (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    probedDirection (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k=CG.direction Q g k := by
  unfold probedDirection
  rw [dc_slide_reference_run memory hm estimate Q hQ hpos g k]
  have hs := fcMethod_static memory Q hQ hpos g (fun j _ => hm j) k
  exact (dc_slide_reference_direction memory estimate Q hQ hpos g k _ hs.2 hs.1).trans
    (retainedMethod_direction memory (fun _ _ => .done) Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k))

/-- The real quadratic sliding DC searched length is exactly the genuine CG
reference length, for arbitrary original observed estimates.
Use: no independent or presumed scalar search value enters native comparison.
Article: main_krylov, thm:DC and thm:dcs.
Proof: actual global CG gradient consistency and the proved original unscaled
direction identify all three true scalar search inputs. -/
theorem dc_slide_quadratic_length (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    dcSearchedLength memory estimate (fun _ => Q) (fun _ => Q) g k=CG.length Q g k := by
  let m := dcSlideMethod memory estimate
  have hg : probedGradient m (fun _ => Q) (fun _ => Q) g k=CG.gradient Q g k :=
    quadratic_gradient_eq_cg m (dc_slide_consistent memory hm estimate) Q hQ hpos g k
  have hd := dc_slide_quadratic_direction memory hm estimate Q hQ hpos g k
  change lineLength (probedGradient m (fun _ => Q) (fun _ => Q) g k)
    (probedDirection m (fun _ => Q) (fun _ => Q) g k) (Q (probedDirection m (fun _ => Q) (fun _ => Q) g k))=_
  rw [hg,hd]

/-- The genuine data-dependent deferred policy using the original observed
arithmetic estimate has its positive reference estimate and class spectral
damping bound on every real nonstagnating quadratic history.
Use: the arithmetic choice in DC's sharp coefficient is the implemented
observed rule, with no assumed interval or true searched length field.
Article: main_krylov, thm:DC, original observed epsilonHat bound.
Proof: both complete original quadratic histories are FC, so the real
deferred observation read by the same estimate is identical to sliding DC's.
Its proved native arithmetic damping bound and actual CG search dictionary
therefore transfer to the true deferred reference estimate. -/
theorem deferred_gauss_radau_reference_damping
    (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k) (horizon : ℕ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hgrad : CG.gradient (cgOperator base) g k≠0) :
    let Q := cgOperator base
    let estimate := dcGaussRadauEstimate memory mu L (n := n)
    let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k
    0<estimate H ∧ |1-CG.length Q g k/estimate H|≤(L-mu)/(L+mu) := by
  let Q := cgOperator base
  let estimate := dcGaussRadauEstimate memory mu L (n := n)
  let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k
  let J := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  have hH : H=J := (deferred_data_reference_run memory hm horizon estimate Q hQ hpos g k).trans
    (dc_slide_reference_run memory hm estimate Q hQ hpos g k).symm
  have hc := dc_gauss_radau_reference_damping memory hm base hb mu L hmu hmuL hlo hhi g k hgrad
  change 0<estimate J ∧ |1-dcSearchedLength memory estimate (fun _ => Q) (fun _ => Q) g k/estimate J|≤(L-mu)/(L+mu) at hc
  rw [dc_slide_quadratic_length memory hm estimate Q hQ hpos g k] at hc
  change 0<estimate H ∧ |1-CG.length Q g k/estimate H|≤(L-mu)/(L+mu)
  rwa [hH]

/-- The original observed arithmetic deferred policy reduces the real full
FC sharp coefficient, strictly at every positive intermediate source budget.
Use: all scalar damping and physical completion domains come from the
implemented native policy's true reference history.
Article: main_krylov, thm:DC, actual Gauss--Radau sharp FC improvement.
Proof: the real observed arithmetic estimate has the proved class spectral
damping bound, strictly below one because the original lower spectral bound
is positive. Apply the genuine full actual CG-tail coefficient comparisons,
including the printed exact intermediate-budget strictness condition. -/
theorem deferred_gauss_radau_FC_improvement
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g=k+1)
    (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    let Q := cgOperator base
    let estimate := dcGaussRadauEstimate fullMemory mu L (n := n)
    let a0 := estimate (methodRun (deferredDataMethod fullMemory (k+1) estimate) (fun _ => Q) (fun _ => Q) g k)
    let epsilon := 1-CG.length Q g k/a0
    (∑ l∈Finset.range k,omega l*‖deferredTail base g k epsilon l‖)≤
      (∑ l∈Finset.range k,omega l*‖cgCanonicalError base g (l+1)‖) ∧
      ((∃ l,l+1<k ∧ 0<omega l) →
        (∑ l∈Finset.range k,omega l*‖deferredTail base g k epsilon l‖)<
          ∑ l∈Finset.range k,omega l*‖cgCanonicalError base g (l+1)‖) := by
  have hc := deferred_gauss_radau_reference_damping fullMemory (fun _ hj => hj) (k+1)
    base hb mu L hmu hmuL hlo hhi g k (cg_nonstagnation base hb g k (by omega))
  have hrho : (L-mu)/(L+mu)<1 := by
    apply (div_lt_one (add_pos (hmu.trans_le hmuL) hmu)).mpr
    linarith
  have hepsilon := hc.2.trans_lt hrho
  exact ⟨deferred_full_coefficient_le_FC base hb g k hstop _ hepsilon.le omega homega,
    fun hp => deferred_full_coefficient_strict_FC base hb g k hstop _ hepsilon omega homega hp⟩

end
end krylov.Cancellation

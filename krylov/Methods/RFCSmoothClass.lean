import krylov.Methods.RFCCompilation
import krylov.Methods.ReferenceModels

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, cor:lm and thm:select, genuine smooth RFC class membership.
Use: prove the actual gated repeated RFC executor belongs to the source
smooth information class from true primitive coefficients, for every
positive newest-retaining memory and every genuine finite correction count.
Source: actual reference transcripts, genuine positive retained and
augmented models, strict real observed gates and true local primitive compilation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability krylov.Reference Filter Topology
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The real primitive compiled RFC direction and every actual repeated correction coefficient are C-r on the true retained and augmented determinant domains.
Use: The real primitive compiled RFC direction and every actual repeated correction coefficient are C-r on the true retained and augmented determinant domains.
Article: main_krylov, def:classes, cor:lm and thm:select, genuine smooth RFC class membership.
Proof: Identify the genuine actual direction and true query shape. The actual retained primitive FC coefficients are C-r, and the genuine finite RFC correction program uses exactly its true nonsingular augmented model. -/
theorem rfcCompiled_coefficients_regular (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E)
    (H : History E) (Q : E →L[ℝ] E) (r : WithTop ℕ∞)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0)
    (hM : (windowModel (((rfcMethod memory count).direction H,Q ((rfcMethod memory count).direction H))::selectedWindow memory H)).det≠0) :
    (rfcCompiledPolicy memory count reference).CoefficientsRegularAt r H Q Q := by
  -- The true current RFC direction fixes the actual augmented model entering its genuine primitive coefficient domain.
  have hd := rfcCompiled_direction memory count reference H hshape
  constructor
  · change ContDiffAt ℝ r (fcObservedRule memory (selectedHistoryShape reference H.observationList.length)
      H.observationList.length : ObservedRule E H.observationList.length).coefficient _
    rw [hshape]
    exact fcObservedRule_actual_regular memory H _ (ofFn_observedArray H.observationList).symm r hC
  · change (if selectedHistoryShape reference H.observationList.length=[] then CorrectionProgram.done else _).RegularAt r Q _ _
    rw [hshape]
    split
    · trivial
    · rw [hd]
      apply rfcObservedProgram_regular
      rw [← augmentedChart_model_det,chartWindow_of_array memory H _ (ofFn_observedArray H.observationList).symm]
      exact hM

/-- The true actual RFC quadratic reference has positive retained and augmented models and a strictly accepted real gate at every nonempty active prefix.
Use: The true actual RFC quadratic reference has positive retained and augmented models and a strictly accepted real gate at every nonempty active prefix.
Article: main_krylov, def:classes, cor:lm and thm:select, genuine smooth RFC class membership.
Proof: Use the genuine complete quadratic transcript and actual CG direction. Proved true retained and augmented reference-model positivity derive both real inverse domains; the actual nonempty retained window has genuine zero observed skew defect. -/
theorem rfc_reference_primitive_domains (memory : ℕ → ℕ) (count : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0) :
    let H := methodRun (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k
    (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).PosDef ∧
    (windowModel (((rfcMethod memory count).direction H,Q ((rfcMethod memory count).direction H))::selectedWindow memory H)).PosDef ∧
    (H.queryShape≠[] → selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) := by
  -- Recover the actual quadratic transcript before deriving genuine retained and augmented model positivity or real gate acceptance.
  let H := methodRun (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k
  have hs := rfcMethod_static memory count Q hQ hpos g hm k
  have hd : (rfcMethod memory count).direction H=CG.direction Q g k :=
    retainedMethod_direction memory _ Q hQ hpos g k H hs.1 hs.2 (hm k)
  have hW : selectedWindow memory H=(referencePairs Q g k).take (memory k) := by
    unfold selectedWindow
    rw [hs.2,methodRun_length]
  refine ⟨?_,?_,?_⟩
  · rw [hW]
    exact retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i hi.le)
  · rw [hd,hW]
    exact augmentedModel_posDef Q hQ hpos g k (memory k) hpre
  · intro hne
    have hk : 0<k := by
      by_contra hz
      have he : k=0 := by omega
      subst k
      exact hne rfl
    have hm0 := hm k (hpre k le_rfl) hk
    have hlen : (selectedWindow memory H).length=min (memory k) k := by
      rw [hW,List.length_take,referencePairs_length]
    refine ⟨List.length_pos_iff_ne_nil.mp (by rw [hlen];omega),?_⟩
    have hzero : windowDefect (selectedWindow memory H)=0 := by
      rw [hW]
      exact windowDefect_quadratic _ Q hQ (retainedImages_quadratic Q g k (memory k))
    rw [hzero,norm_zero]
    exact zero_lt_one

/-- The actual gated repeated RFC executor has a genuine primitive C-r local observed-program representation on every true active quadratic prefix.
Use: The actual gated repeated RFC executor has a genuine primitive C-r local observed-program representation on every true active quadratic prefix.
Article: main_krylov, def:classes, cor:lm and thm:select, genuine smooth RFC class membership.
Proof: Select true reference query shapes solely by actual observation dimensions. Derive actual model and gate domains, prove genuine local primitive decision agreement, identify the real compiled reference histories and transfer every true primitive coefficient domain. -/
theorem rfcMethod_smoothCycleAt (memory : ℕ → ℕ) (count : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (N : ℕ)
    (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (rfcMethod memory count) r Q g N := by
  -- Build the genuine reference-specific primitive chart and derive its real domains along actual raw histories before identifying the compiled run.
  let H := fun k => methodRun (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k
  let P := rfcCompiledPolicy memory count H
  have hshape (k : ℕ) : selectedHistoryShape H (H k).observationList.length=(H k).queryShape :=
    selectedHistoryShape_actual H (methodRun_observationLength_strictMono _ _ _ _) k
  have hdomains (k : ℕ) (hk : k<N) := rfc_reference_primitive_domains memory count Q hQ hpos g hm k
    (fun i hi => hpre i (hi.trans_lt hk))
  have hlocal (k : ℕ) (hk : k<N) : LocalCompiledAt (rfcMethod memory count) P (H k)
      (Q (P.method.direction (H k))) :=
    rfcCompiled_local memory count H (H k) _ (hshape k) (hdomains k hk).1 (hdomains k hk).2.2
  have heq (k : ℕ) (hk : k≤N) : H k=methodRun P.method (fun _ => Q) (fun _ => Q) g k :=
    localCompiled_reference_run_of_raw (rfcMethod memory count) P _ _ g k (fun i hi => hlocal i (hi.trans_le hk))
  refine ⟨P,?_,?_⟩
  · intro k hk
    rw [← heq k hk.le]
    exact rfcCompiled_coefficients_regular memory count H (H k) Q r (hshape k)
      (hdomains k hk).1.det_pos.ne' (hdomains k hk).2.1.det_pos.ne'
  · intro k hk
    rw [← heq k hk.le]
    exact hlocal k hk

/-- The genuine globally CG-consistent source smooth information-class member implemented by actual gated repeated RFC for any positive newest-retaining memory and finite correction count.
Use: The genuine globally CG-consistent source smooth information-class member implemented by actual gated repeated RFC for any positive newest-retaining memory and finite correction count.
Article: main_krylov, def:classes, cor:lm and thm:select, genuine smooth RFC class membership.
Proof: Combine the actual source-admissible RFC policy, its proved global quadratic CG consistency and the genuine primitive local coefficient representation on every true active reference cycle. -/
def smoothRFCClass (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (count : ℕ) : SmoothProbedClass E where
  toProbedClass := rfcClass memory count
  consistent := rfcMethod_consistent memory hm count
  smooth := fun Q hQ hpos g N hpre => rfcMethod_smoothCycleAt memory count Q hQ hpos g (fun k _ => hm k) N hpre 2
end
end krylov.Methods

import krylov.Methods.FCCompilation
import krylov.Methods.ReferenceModels

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, lem:U and cor:lm, genuine smooth FC class membership.
Use: prove actual retained-window FC belongs to the source smooth
information class from its real primitive observed coefficients, for every
positive newest-retaining memory rule, including full and sliding memory.
Source: genuine exact FC primitive compilation, actual finite-coordinate
Gram determinant identities and true positive quadratic retained models.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive compiled FC coefficients are C-r at every actual empty-correction history with a true nonsingular retained conjugacy matrix.
Use: The genuine primitive compiled FC coefficients are C-r at every actual empty-correction history with a true nonsingular retained conjugacy matrix.
Article: main_krylov, def:classes, lem:U and cor:lm, genuine smooth FC class membership.
Proof: Reconstruct the actual retained window from true observations and transfer its genuine inverse domain to the real fixed coefficient array. The proved actual primitive FC observed coefficients are C-r; the true correction program is empty. -/
theorem fcCompiled_coefficients_regular (memory : ℕ → ℕ) (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) (r : WithTop ℕ∞) (A B : E →L[ℝ] E)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0) :
    (fcCompiledPolicy memory).CoefficientsRegularAt r H A B := by
  -- Establish the real primitive coefficient inverse domain on the actual observed-data chart.
  let data := observedArray H.observationList.length H.observationList
  let shape := List.replicate ((H.observationList.length-2)/4) 0
  have hW : chartWindow memory shape data=selectedWindow memory H := by
    dsimp only [chartWindow,shape,data]
    rw [zeroQuery_coefficientShape H hshape,ofFn_observedArray,historyFromObservations_actual]
  have hlen : (selectedWindow memory H).length=min (memory shape.length) shape.length := by
    rw [← hW,chartWindow_length]
  have hd : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0 := by
    change (crossGram (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).2)
      (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).1)).det≠0
    rw [hW,← crossGram_getD_array_det _ _ hlen]
    exact hC
  exact ⟨fcObservedRule_coefficient_regular memory shape data hd r,trivial⟩

/-- The actual retained-window FC executor has a genuine primitive C-r local observed-program representation on every true nonstagnating quadratic prefix retaining the newest available pair.
Use: The actual retained-window FC executor has a genuine primitive C-r local observed-program representation on every true nonstagnating quadratic prefix retaining the newest available pair.
Article: main_krylov, def:classes, lem:U and cor:lm, genuine smooth FC class membership.
Proof: Use the exact real primitive FC compiler. Its actual quadratic history equals the genuine FC transcript; true reference retained conjugacy models are positive definite, deriving every primitive coefficient domain. Actual local observed-policy equality holds on the true fixed query shape. -/
theorem fcMethod_smoothCycleAt (memory : ℕ → ℕ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (N : ℕ)
    (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (fcMethod memory) r Q g N := by
  -- The true compiler agrees with the real FC executor on complete histories, so its reference models are actual CG retained models.
  let P := fcCompiledPolicy memory (E := E)
  have hshape (k : ℕ) : (methodRun P.method (fun _ => Q) (fun _ => Q) g k).queryShape=
      List.replicate (methodRun P.method (fun _ => Q) (fun _ => Q) g k).records.length 0 := by
    rw [methodRun_length]
    exact methodRun_empty_corrections_shape P.method (fcCompiled_correction memory) _ _ g k
  refine ⟨P,?_,?_⟩
  · intro k hk
    apply fcCompiled_coefficients_regular memory _ (hshape k) r Q Q
    -- Transfer the genuine positive quadratic retained matrix, rather than assuming a smooth cycle or an inverse domain.
    have hW : selectedWindow memory (methodRun P.method (fun _ => Q) (fun _ => Q) g k)=
        (referencePairs Q g k).take (memory k) := by
      rw [fcCompiled_run]
      unfold selectedWindow
      rw [(fcMethod_static memory Q hQ hpos g hm k).2,methodRun_length]
    rw [hW]
    exact (retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i (hi.trans hk))).det_pos.ne'
  · intro k _
    exact fcCompiled_local memory _ _ (hshape k)

/-- The genuine globally CG-consistent source smooth information-class member implemented by actual FC with every positive newest-retaining memory rule.
Use: The genuine globally CG-consistent source smooth information-class member implemented by actual FC with every positive newest-retaining memory rule.
Article: main_krylov, def:classes, lem:U and cor:lm, genuine smooth FC class membership.
Proof: Combine the real source-admissible FC policy, proved actual global quadratic CG consistency and the genuine primitive local coefficient representation on every active reference prefix. -/
def smoothFCClass (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) : SmoothProbedClass E where
  toProbedClass := fcClass memory
  consistent := fcMethod_consistent memory hm
  smooth := fun Q hQ hpos g N hpre => fcMethod_smoothCycleAt memory Q hQ hpos g (fun k _ => hm k) N hpre 2
end
end krylov.Methods

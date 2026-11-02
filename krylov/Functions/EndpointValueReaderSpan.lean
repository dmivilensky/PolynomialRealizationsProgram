import krylov.Functions.EndpointValueReader
import krylov.Methods.HistoryModelArrays
import krylov.Methods.FinalizedInformation

/-!
Article: main_krylov, def:classes(M^F) and thm:Fplanar, concrete class admission.
Use: derive the original retained-span and searched-gradient dictionaries
for the actual endpoint reader, rather than assuming a reader certificate.
Consequently the globally continued original method executes precisely the
finite observed one-correction rule on every real final history.
Source: actual stored pair membership, true current line scaling, and the
already proved global quadratic-consistency compiler.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cached old chronological step is a genuine retained-window column;
an unavailable old index is the actual zero default.
Article: main_krylov, thm:Fplanar, concrete endpoint reader. -/
theorem endpointPastStep_mem (m : ProbedMethod E) (H : History E) (z : E) (i : ℕ) :
    endpointPastStep H i∈Submodule.span ℝ
      (Set.range (windowSteps (valueCurrentWindow m H z))) := by
  have he : endpointPastStep H i=(H.pairs.reverse.getD i (0,0)).1 := by
    unfold endpointPastStep
    rw [List.getD_eq_getElem?_getD]
    cases H.pairs.reverse[i]? <;> rfl
  rw [he]
  apply (windowSpan_mono H.pairs.reverse (valueCurrentWindow m H z) ?_)
    (getD_step_mem_windowSpan H.pairs.reverse i)
  intro p hp
  exact List.mem_cons.mpr (Or.inr (List.mem_reverse.mp hp))

/-- The true current line step is a scalar multiple of the actually
observed current direction, hence lies in the allowed augmented span.
Article: main_krylov, thm:Fplanar, concrete endpoint reader. -/
theorem endpointCurrentStep_mem (m : ProbedMethod E) (H : History E) (z : E) :
    endpointCurrentStep m H z∈Submodule.span ℝ
      (Set.range (windowSteps (valueCurrentWindow m H z))) := by
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨0,by simp [valueCurrentWindow]⟩,rfl⟩

/-- Every step returned by the genuine endpoint reader belongs to the
original current/retained step span, for arbitrary cached scalar values
and arbitrary actual histories. No trajectory condition is assumed.
Article: main_krylov, thm:Fplanar, original class bridge. -/
theorem endpointValueReader_steps_mem (m : ProbedMethod E) (N : ℕ)
    (f : E → ℝ) (x₀ : E) (H : History E) (z : E) (i : Fin N) :
    (endpointValueReader m N f x₀ H z).lineSteps i∈Submodule.span ℝ
      (Set.range (windowSteps (valueCurrentWindow m H z))) := by
  change (if i.val+1=N then endpointCurrentStep m H z else endpointPastStep H i.val)∈_
  split
  · exact endpointCurrentStep_mem m H z
  · exact endpointPastStep_mem m H z i.val

/-- The actual globally continued method with the concrete endpoint reader
executes exactly the finite value rule at its true final iteration.
The searched-gradient and retained-span conditions are proved internally.
Article: main_krylov, thm:Fplanar, genuine original-class realization. -/
theorem OneCorrectionValueMethod.endpoint_global_final_exact {N : ℕ}
    (M : OneCorrectionValueMethod E N) (hN : 0<N) (f : E → ℝ) (x₀ : E)
    (H : History E) (z : E) (hfinal : H.records.length+1=N) :
    (M.globalMethod hN (endpointValueReader M.gradientPolicy N f x₀)).correction H z=
      observedSpanFinalTree hN M.coefficients H (endpointValueReader M.gradientPolicy N f x₀ H z) :=
  M.globalMethod_final_exact hN _ H z hfinal
    (endpointValueReader_final_gradient M.gradientPolicy N f x₀ H z)
    (endpointValueReader_steps_mem M.gradientPolicy N f x₀ H z)


/-- The genuine known-budget centre with a concrete actual endpoint reader,
unchanged full-memory FC prefix and global full-memory continuation.
Article: main_krylov, thm:Fplanar, attained original-class witness. -/
def budgetedCentreEndpointMethod {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ) (hN : 0<N)
    (f : E → ℝ) (x₀ : E) : ProbedMethod E :=
  budgetedCentreGlobalMethod S B hN (endpointValueReader (fcMethod fullMemory) N f x₀)

/-- The concrete endpoint-only centre is globally CG-consistent on every
positive quadratic, including every future solved tail.
Article: main_krylov, thm:Fplanar. -/
theorem budgetedCentreEndpointMethod_consistent {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ)
    (hN : 0<N) (f : E → ℝ) (x₀ : E) :
    CGConsistent (budgetedCentreEndpointMethod S B hN f x₀) :=
  budgetedCentreGlobalMethod_consistent S B hN _

/-- The concrete centre satisfies every original information-span
restriction on every actual input history. Article: def:classes(M^F). -/
theorem budgetedCentreEndpointMethod_admissible {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ)
    (hN : 0<N) (f : E → ℝ) (x₀ : E) :
    ProbedSpanRestricted fullMemory (budgetedCentreEndpointMethod S B hN f x₀) :=
  budgetedCentreGlobalMethod_admissible S B hN _

/-- The actual concrete centre makes at most one correction query per
iteration, through the entire continued execution. Article: thm:Fplanar. -/
theorem budgetedCentreEndpointMethod_one {N : ℕ} (S : E ≃L[ℝ] E) (B : ℝ)
    (hN : 0<N) (f : E → ℝ) (x₀ : E) (H : History E) (z : E) :
    CorrectionTree.AtMostOne ((budgetedCentreEndpointMethod S B hN f x₀).correction H z) :=
  budgetedCentreGlobalMethod_one S B hN _ H z

end
end krylov.Functions

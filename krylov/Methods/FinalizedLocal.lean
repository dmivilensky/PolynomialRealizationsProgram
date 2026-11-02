import krylov.Methods.FinalizedCompilation

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine local primitive final-wrapper bridge.
Use: prove actual raw and primitive compiled final-correction policies
agree on true finite observed-data neighborhoods with their genuine
record and correction-query boundaries.
Source: actual original local primitive policy charts, true selected
reference observation dimensions and genuine whole-tree appended model equality.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine local primitive representation of the actual original policy yields a true local primitive representation of its real final latest-model wrapper, including the genuine subsequent FC continuation.
Use: A genuine local primitive representation of the actual original policy yields a true local primitive representation of its real final latest-model wrapper, including the genuine subsequent FC continuation.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine local primitive final-wrapper bridge.
Proof: Fixed actual query shape determines the true record count and observation dimension throughout the genuine observed neighborhood. Transfer real original whole-tree agreement before the horizon; afterwards actual FC directions and empty correction programs agree on the whole true chart. -/
theorem finalizedCompiled_local (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (N : ℕ) (reference : ℕ → History E) (H₀ : History E) (z₀ : E)
    (hshape₀ : selectedHistoryShape reference H₀.observationList.length=H₀.queryShape)
    (hlocal : H₀.records.length<N → LocalCompiledAt m P H₀ z₀) :
    LocalCompiledAt (finalizedMethod m N) (finalizedCompiledPolicy P N reference) H₀ z₀ := by
  -- Genuine fixed query boundaries and actual finite observation dimension preserve the real earlier or later policy branch throughout the true neighborhood.
  intro n data hdata
  by_cases hk : H₀.records.length<N
  · obtain ⟨V,hV,hm⟩ := hlocal hk n data hdata
    refine ⟨V,hV,?_⟩
    intro q hq H hshape hobs
    have hlen : H.records.length=H₀.records.length := by
      have he := congrArg List.length hshape
      simpa only [History.queryShape,List.length_map] using he
    have hdim : H.observationList.length=H₀.observationList.length := by
      rw [hobs,hdata,List.length_ofFn,List.length_ofFn]
    have hs : selectedHistoryShape reference H.observationList.length=H.queryShape := by
      rw [hdim,hshape₀,← hshape]
    exact finalizedCompiled_matches_before m P N reference H q.2 hs (by omega) (hm q hq H hshape hobs)
  · refine ⟨Set.univ,Filter.univ_mem,?_⟩
    intro q _ H hshape hobs
    have hlen : H.records.length=H₀.records.length := by
      have he := congrArg List.length hshape
      simpa only [History.queryShape,List.length_map] using he
    have hdim : H.observationList.length=H₀.observationList.length := by
      rw [hobs,hdata,List.length_ofFn,List.length_ofFn]
    have hs : selectedHistoryShape reference H.observationList.length=H.queryShape := by
      rw [hdim,hshape₀,← hshape]
    exact finalizedCompiled_matches_after m P N reference H q.2 hs (by omega)
end
end krylov.Methods

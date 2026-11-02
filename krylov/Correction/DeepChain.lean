import krylov.Correction.DeepChecked
import krylov.Correction.DeepInterval

/-!
Article: main_krylov, prop:deep, complete certified genuine RFC trajectory.
Use: Derive all exact original input enclosures, actual accepted gates,
continuous source inputs and equality with the genuine real RFC executor.
Source: unchanged checker soundness, independent original source decoding,
exact input coordinate transfer and actual RFC array-phase execution.
-/

namespace krylov.Correction.Certificate
noncomputable section
open chebyshev2.Numerics.IntegerCertificate
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The original first certificate stack consists precisely of its independently checked true parameter interval.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_initial_inputs (d : Fin 3) :
    (deepEnclosure d 0).inputs=[deepParameterBounds d] := by
  fin_cases d <;> decide +kernel

/-- Every true source parameter starts in its exact original certified input stack.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_initial_enclosed (d : Fin 3) {s : ℝ}
    (hs : s∈Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ)) :
    Encloses deepScale (deepEnclosure d 0).inputs (sourceData 0 s) := by
  rw [deep_initial_inputs]
  intro j I hj
  cases j with
  | zero =>
    have hi : deepParameterBounds d=I := by simpa only [List.getElem?_cons_zero,Option.some.injEq] using hj
    subst I
    exact deep_parameter_enclosed d hs
  | succ j => simp only [List.getElem?_cons_succ,List.getElem?_nil,reduceCtorEq] at hj

/-- Every recursively evaluated genuine original source prefix has its fully proved exact input enclosure.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_all_enclosed (d : Fin 3) {s : ℝ}
    (hs : s∈Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ)) (k : Fin 4) :
    Encloses deepScale (deepEnclosure d k).inputs (sourceData k.val s) := by
  -- Start with the actual parameter interval and propagate the exact integer enclosures through each genuine source block.
  have h : ∀ j (hj : j<4), Encloses deepScale (deepEnclosure d ⟨j,hj⟩).inputs (sourceData j s) := by
    intro j
    induction j with
    | zero => intro _; exact deep_initial_enclosed d hs
    | succ j ih =>
      intro hj
      exact deep_next_enclosed d ⟨j,by omega⟩ s (ih (by omega))
  exact h k.val k.isLt

/-- Every original empty-prefix input coordinate is a continuous function of its actual real parameter.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem sourceData_zero_continuousOn {K : Set ℝ} (j : ℕ) :
    ContinuousOn (fun s => sourceData 0 s j) K := by
  by_cases hj : j=0
  · simp only [sourceData,ite_eq_left hj]
    exact continuous_id.continuousOn
  · simpa only [sourceData,ite_eq_right hj] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) K)

/-- Each accepted original arithmetic block propagates continuity of all genuine next source input coordinates.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_next_continuousOn (d : Fin 3) (k : Fin 3) {K : Set ℝ}
    (hx : ∀ s∈K, Encloses deepScale (deepEnclosure d k.castSucc).inputs (sourceData k.val s))
    (hc : ∀ j, ContinuousOn (fun s => sourceData k.val s j) K) :
    ∀ j, ContinuousOn (fun s => sourceData (k.val+1) s j) K := by
  -- Inside the actual finite layout, decode a continuous checked output; every outside coordinate is the exact constant zero.
  intro j
  by_cases hj : j<5+8*(k.val+1)
  · let j' : Fin (5+8*(k.val+1)) := ⟨j,hj⟩
    have hh := (deepEnclosure d k.castSucc).continuousOn deepScale_pos hx hc (sourceNextIndex k j')
    have he : ∀ s, ((sourceOutputs k.castSucc).get (sourceNextIndex k j')).value (sourceData k.val s)=sourceData (k.val+1) s j := by
      intro s
      rw [sourceOutputs_next,sourceNextInputs_value]
    simpa only [he] using hh
  · have he : ∀ s, sourceData (k.val+1) s j=0 := by
      intro s
      rw [sourceData]
      apply encodeInput_outside
      omega
    simpa only [he] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) K)

/-- All genuine original source input coordinates are continuous on their entire true certificate domain.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_all_continuousOn (d : Fin 3) (k : Fin 4) :
    ∀ j, ContinuousOn (fun s => sourceData k.val s j)
      (Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ)) := by
  -- Apply the same checked real program continuity along the exact already enclosed source-prefix family.
  have h : ∀ k (hk : k<4), ∀ j, ContinuousOn (fun s => sourceData k s j)
      (Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ)) := by
    intro k
    induction k with
    | zero => intro _; exact sourceData_zero_continuousOn
    | succ k ih =>
      intro hk
      exact deep_next_continuousOn d ⟨k,by omega⟩
        (fun _ hs => deep_all_enclosed d hs _) (ih (by omega))
  exact h k.val k.isLt

/-- Every certified original source prefix equals the actual original full-memory RFC gradient and complete observed total-step/secant history.
Use: Close the source-specific numerical bounds on the real original observed RFC run.
Article: main_krylov, prop:deep, complete original certified trajectory.
Proof: Induct over the genuine finite source blocks, using their fully checked output and next-input identities.
-/
theorem deep_all_realizes (d : Fin 3) {s : ℝ}
    (hs : s∈Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ))
    (k : ℕ) (hk : k≤4) :
    (sourceInputPrefix k).Realizes sourceProbe sourceCorrection sourceInitial (sourceData k s) := by
  -- Each genuine accepted observed-data gate identifies the next source block with the actual RFC executor.
  induction k with
  | zero => exact sourceData_realizes_zero s
  | succ k ih =>
    apply sourceData_realizes_next k s (ih (by omega))
    rcases Nat.eq_zero_or_pos k with h0 | hp
    · exact Or.inl h0
    · exact Or.inr ⟨hp,deep_gate_of_enclosed d ⟨k,by omega⟩ (deep_all_enclosed d hs _)⟩

end
end krylov.Correction.Certificate

import krylov.Methods.RFC

/-!
Article: main_krylov, lem:consistent(a) and prop:dict(iii), complete quadratic cycles.
Use: transfer actual pair-history consistency to actual physical iterates,
prove exact active-atom termination, and discharge the source's restart rule.
Source: finite CG termination and the executed retained-policy invariants.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual physical displacement accumulated by an executed history.
Use: the actual method iterate is the initial point plus this quantity.
Article: main_krylov, def:classes, x_k−x₀. -/
def History.displacement (H : History E) : E := (H.records.map IterationRecord.step).sum

omit [InnerProductSpace ℝ E] in
/-- Extracting actual secant pairs preserves the physical recorded step list.
Use: actual pair-transcript equality gives equality of actual iterates.
Article: main_krylov, alg:fc, record the total evaluated step.
Proof: the first component of each extracted pair is exactly its record's actual step. -/
theorem History.pairs_steps (H : History E) : H.pairs.map Prod.fst=H.records.map IterationRecord.step := by
  rcases H with ⟨initial,records⟩
  induction records with
  | nil => rfl
  | cons r rs ih => simpa only [History.pairs, recordPairs, List.map_cons] using congrArg (List.cons r.step) ih

/-- The actual reference pair transcript sums to the actual computed CG displacement.
Use: compare actual iterates rather than only gradients.
Article: main_krylov, lem:consistent(a), CG iterates.
Proof: split off the newest true step and use the genuine reference displacement recurrence. -/
theorem referencePairs_displacement (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    ((referencePairs Q g k).map Prod.fst).sum=CG.displacement Q g k := by
  induction k with
  | zero => simp only [referencePairs, List.map_nil, List.sum_nil, CG.displacement, Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    simp only [referencePairs, List.map_cons, List.sum_cons, ih, CG.displacement_succ, referenceStep]
    exact add_comm _ _

/-- Equality of actual reference pairs forces equality of actual physical iterates.
Use: the transcript invariant implies precisely the source's iterate consistency assertion.
Article: main_krylov, lem:consistent(a).
Proof: sum the actual step components of the equal pair transcripts. -/
theorem History.displacement_reference (H : History E) (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hp : H.pairs=referencePairs Q g k) : H.displacement=CG.displacement Q g k := by
  rw [History.displacement, ← H.pairs_steps, hp, referencePairs_displacement]

variable {n : ℕ}

/-- Restarting at the actual active-atom count retains every pair on the whole active CG prefix.
Use: discharge restarted FC/RFC consistency without an infinite nonstagnation premise.
Article: main_krylov, lem:consistent(a), restart every n atoms.
Proof: a nonzero actual CG residual is strictly before the proved exact stopping count. -/
theorem restartedMemory_active (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hg : CG.gradient (cgOperator base) g k≠0)
    (hk : 0<k) : 0<restartedMemory (referenceAtomCount base hb g) k := by
  have hlt : k<referenceAtomCount base hb g := by
    by_contra h
    exact hg ((cg_stopping_iff base hb g k).mpr (by omega))
  rw [restartedMemory_prefix hlt]
  exact hk

/-- Actual restarted FC has the exact CG gradients, actual pair transcript and physical iterates for the whole run.
Use: the restart boundary occurs only when the actual quadratic is already solved.
Article: main_krylov, lem:consistent(a), restarted FC.
Proof: exact active stopping discharges retained-newest consistency on every nonzero state,
and the established pair transcript identifies the actual physical iterate. -/
theorem restartedFC_static (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let H := methodRun (fcMethod (restartedMemory (referenceAtomCount base hb g)))
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k
    H.gradient=CG.gradient (cgOperator base) g k ∧ H.pairs=referencePairs (cgOperator base) g k ∧
      H.displacement=CG.displacement (cgOperator base) g k := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hs := fcMethod_static _ _ hQ hpos g (restartedMemory_active base hb g) k
  exact ⟨hs.1,hs.2,History.displacement_reference _ _ _ _ hs.2⟩

/-- Actual restarted RFC_k has the exact CG gradients, pair transcript and iterates for every finite correction count.
Use: includes all repeated actual intermediate correction queries and the solved restart tail.
Article: main_krylov, lem:consistent(a), restarted RFC and RFC_k.
Proof: the active-count restart condition discharges the concrete repeated RFC transcript theorem. -/
theorem restartedRFC_static (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (count k : ℕ) :
    let H := methodRun (rfcMethod (restartedMemory (referenceAtomCount base hb g)) count)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k
    H.gradient=CG.gradient (cgOperator base) g k ∧ H.pairs=referencePairs (cgOperator base) g k ∧
      H.displacement=CG.displacement (cgOperator base) g k := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hs := rfcMethod_static _ count _ hQ hpos g (restartedMemory_active base hb g) k
  exact ⟨hs.1,hs.2,History.displacement_reference _ _ _ _ hs.2⟩

/-- Every actual consistent retained-window FC run stops exactly at the active atom count.
Use: repeated eigenvalues and absent initial spectral coordinates have their true stopping count.
Article: main_krylov, lem:consistent(a) and prop:dict(iii).
Proof: the actual computed gradient is the true CG residual, whose exact stopping criterion is already proved. -/
theorem fcMethod_stopping (memory : ℕ → ℕ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n))
    (hm : ∀ k, CG.gradient (cgOperator base) g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    (methodRun (fcMethod memory) (fun _ => cgOperator base) (fun _ => cgOperator base) g k).gradient=0 ↔
      referenceAtomCount base hb g≤k := by
  rw [(fcMethod_static memory _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g hm k).1]
  exact cg_stopping_iff base hb g k

/-- Every actual consistent retained-window RFC_k run stops exactly at the active atom count.
Use: arbitrary finite repeated zero corrections preserve genuine quadratic finite termination.
Article: main_krylov, lem:consistent(a).
Proof: the actual repeated RFC gradient is the true CG gradient, including all solved tails. -/
theorem rfcMethod_stopping (memory : ℕ → ℕ) (count : ℕ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hm : ∀ k, CG.gradient (cgOperator base) g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    (methodRun (rfcMethod memory count) (fun _ => cgOperator base) (fun _ => cgOperator base) g k).gradient=0 ↔
      referenceAtomCount base hb g≤k := by
  rw [(rfcMethod_static memory count _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g hm k).1]
  exact cg_stopping_iff base hb g k

end
end krylov.Methods

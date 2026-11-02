import krylov.Methods.RetainedSolve
import krylov.Methods.QuadraticConsistency
import krylov.Reference.Iterates

/-!
Article: main_krylov, alg:fc and lem:consistent(a), executed FC policies.
Use: construct the actual nonanticipating retained-window policies and prove
their gradients, stored pairs and iterates equal the executed CG reference.
Source: block conjugacy with exact search, KoldaEtAl98; all inverses and
history identities are derived from the actual data rather than assumed.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual retained-window policy with an observed-data correction rule.
Use: FC and RFC share precisely the same direction and actual retention implementation.
Article: main_krylov, alg:fc, FC/RFC branch. -/
def retainedMethod (memory : ℕ → ℕ) (correction : History E → E → CorrectionTree E) : ProbedMethod E where
  direction H := windowDirection (selectedWindow memory H) H.gradient
  correction := correction

/-- The concrete FC policy with the prescribed actual pair retention.
Use: full, restarted and sliding FC are actual members of the probed information protocol.
Article: main_krylov, alg:fc, no correction. -/
def fcMethod (memory : ℕ → ℕ) : ProbedMethod E := retainedMethod memory (fun _ _ => .done)

/-- The direction computed from a reference transcript is the actual CG direction.
Use: the implementation reads the observed list length and retained pairs, with no hidden reference clock.
Article: main_krylov, lem:consistent(a).
Proof: pair extraction preserves the iteration count; substitute the actual
reference pairs and invoke the proved retained-window solve, including stopped tails. -/
theorem retainedMethod_direction (memory : ℕ → ℕ) (correction : History E → E → CorrectionTree E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hm : CG.gradient Q g k≠0 → 0<k → 0<memory k) :
    (retainedMethod memory correction).direction H=CG.direction Q g k := by
  have hl : H.records.length=k := by
    rw [← H.pairs_length, hp, referencePairs_length]
  change windowDirection (H.pairs.take (memory H.records.length)) H.gradient=_
  rw [hl, hp, hg]
  exact windowDirection_reference_all Q hQ hpos g k (memory k) hm

/-- One real zero-correction quadratic iteration records exactly the actual CG pair.
Use: the reference comparison controls the complete stored secant data, not only its gradient.
Article: main_krylov, lem:consistent(a), inductive actual history update.
Proof: execute the actual zero correction tree, use the actual search direction,
and identify the new secant with the true operator applied to the actual CG step. -/
theorem reference_advance (m : ProbedMethod E) (Q : E →L[ℝ] E) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hd : m.direction H=CG.direction Q g k)
    (hz : ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) :
    (methodAdvance m Q Q H).gradient=CG.gradient Q g (k+1) ∧
      (methodAdvance m Q Q H).pairs=referencePairs Q g (k+1) := by
  -- Executing a zero correction phase preserves both the actual line displacement and its actual observed gradient.
  have he := (zeroCorrections_change_operator _ Q Q _ hz).2
  have hs : searchedGradient H.gradient (m.direction H) (Q (m.direction H))=CG.gradient Q g (k+1) := by
    rw [hg, hd]; rfl
  constructor
  · change (runCorrections _ Q _).gradient=_
    rw [he.2, hs]
  · change ((lineLength H.gradient (m.direction H) (Q (m.direction H)) • m.direction H+
      (runCorrections _ Q _).movement,
      (runCorrections _ Q _).gradient-H.gradient)::H.pairs)=_
    rw [he.1, he.2, add_zero, hs, hg, hd, hp]
    change (referenceStep Q g k, CG.gradient Q g (k+1)-CG.gradient Q g k)::referencePairs Q g k=_
    rw [CG.gradient_succ, add_sub_cancel_left]
    simp only [referencePairs, referenceStep, map_smul]

/-- The actual retained-window run agrees with the true reference transcript when its actual quadratic corrections vanish.
Use: one execution proof covers FC and every finite repeated RFC correction rule.
Article: main_krylov, lem:consistent(a), complete quadratic history invariant.
Proof: induct on the executed policy, deriving its direction from its actual
stored reference pairs before applying the proved actual zero-correction update. -/
theorem retainedMethod_static (memory : ℕ → ℕ) (correction : History E → E → CorrectionTree E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k)
    (hc : ∀ k (H : History E), H.gradient=CG.gradient Q g k → H.pairs=referencePairs Q g k →
      let m := retainedMethod memory correction
      ZeroCorrections (correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) (k : ℕ) :
    let H := methodRun (retainedMethod memory correction) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k := by
  -- The actual transcript is established before using any of the retained-window solve identities.
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    exact reference_advance _ Q g k _ ih.1 ih.2
      (retainedMethod_direction memory correction Q hQ hpos g k _ ih.1 ih.2 (hm k))
      (hc k _ ih.1 ih.2)

/-- Concrete FC generates exactly the true quadratic gradients and the true recorded secants.
Use: establishes full and every positive sliding-window FC by actual execution, including solved tails.
Article: main_krylov, lem:consistent(a).
Proof: the actual FC correction tree is empty, so the executed retained-method invariant applies. -/
theorem fcMethod_static (memory : ℕ → ℕ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    let H := methodRun (fcMethod memory) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k :=
  retainedMethod_static memory _ Q hQ hpos g hm (by intros; trivial) k

/-- Concrete FC with every always-retaining-newest memory rule is globally CG-consistent.
Use: transfers the exact lower bounds for all CG-consistent policies to the actual FC implementation.
Article: main_krylov, lem:consistent(a), full and sliding memories.
Proof: the actual transcript theorem identifies the implemented direction with
the actual CG direction; FC has scale one and no correction coefficients. -/
theorem fcMethod_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) :
    CGConsistent (fcMethod memory : ProbedMethod E) := by
  intro Q hQ hpos g k
  have hs := fcMethod_static memory Q hQ hpos g (fun k _ => hm k) k
  refine ⟨1, zero_lt_one, ?_, trivial⟩
  change (retainedMethod memory _).direction _=1 • CG.direction Q g k
  rw [one_smul]
  exact retainedMethod_direction memory _ Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)

/-- Full-memory FC is genuinely globally CG-consistent.
Use: identifies the actual full-cycle FC policy used in the first-variation analysis.
Article: main_krylov, lem:consistent(a).
Proof: full retention keeps the newest pair at every positive iteration. -/
theorem fullFC_consistent : CGConsistent (fcMethod fullMemory : ProbedMethod E) :=
  fcMethod_consistent _ (fun _ hk => hk)

/-- Every positive sliding-window FC policy is genuinely globally CG-consistent.
Use: the memory parameter may be smaller than the active spectral atom count.
Article: main_krylov, lem:consistent(a), m≥1.
Proof: a positive fixed window always retains the newest actual pair. -/
theorem slidingFC_consistent {m : ℕ} (hm : 0<m) :
    CGConsistent (fcMethod (slidingMemory m) : ProbedMethod E) :=
  fcMethod_consistent _ (fun _ _ => hm)

end
end krylov.Methods

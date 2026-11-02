import bezout.History.Oracle
import bezout.History.Realization
import chebyshev1.Algebra.Multilinear

/-!
Article: bezout, Appendix D, the finite-noise multilinear expansion.
Use: represents an actual arbitrary-dimensional causal execution by a product
of affine prediction-state operators, with one fresh perturbation per call.
Proof: the prediction invariant stores the initial point minus already observed
answers; triangularity makes each query slot stable after its own call.
-/

namespace bezout.Channel
noncomputable section
open Polynomial chebyshev1
open scoped BigOperators
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Prediction slots for every physical query and the terminal output. -/
abbrev PredictionSpace (N : ℕ) (E : Type*) := Option (Fin N) → E

/-- The rank-one change of every prediction caused by one actual oracle answer. -/
def predictionInsertion (h : bezout.History N) (s : Fin N) (L : E →ₗ[ℝ] E) :
    Module.End ℝ (PredictionSpace N E) where
  toFun v i := -(h.predictionCoefficient i s • L (v (some s)))
  map_add' v w := by ext i; simp [smul_add, add_comm]
  map_smul' c v := by ext i; simp [smul_smul, mul_comm]

/-- One exact physical prediction stage for a linear time-dependent oracle. -/
def predictionStage (h : bezout.History N) (s : Fin N) (L : E →ₗ[ℝ] E) :
    Module.End ℝ (PredictionSpace N E) := 1+predictionInsertion h s L

/-- The physical action of one prediction stage. -/
@[simp] theorem predictionStage_apply (h : bezout.History N) (s : Fin N)
    (L : E →ₗ[ℝ] E) (v : PredictionSpace N E) (i : Option (Fin N)) :
    predictionStage h s L v i=v i-h.predictionCoefficient i s • L (v (some s)) := by
  simp [predictionStage, predictionInsertion, sub_eq_add_neg]

/-- Extend the actual stage sequence by identities beyond the finite horizon. -/
def predictionStageNat (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E) (k : ℕ) :
    Module.End ℝ (PredictionSpace N E) := if hk : k<N then predictionStage h ⟨k,hk⟩ (L ⟨k,hk⟩) else 1

/-- Actual prediction state after a chronological prefix of physical calls. -/
def predictionPrefix (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) (k : ℕ) : PredictionSpace N E :=
  orderedProduct (predictionStageNat h L) k (fun _ => initial)

/-- The prediction state starts with the supplied initial point in every slot. -/
@[simp] theorem predictionPrefix_zero (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) : predictionPrefix h L initial 0=fun _ => initial := by simp [predictionPrefix]

/-- Chronological recurrence of the actual prediction state. -/
theorem predictionPrefix_succ (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) (k : ℕ) (hk : k<N) (i : Option (Fin N)) :
    predictionPrefix h L initial (k+1) i=predictionPrefix h L initial k i-
      h.predictionCoefficient i ⟨k,hk⟩ • L ⟨k,hk⟩ (predictionPrefix h L initial k (some ⟨k,hk⟩)) := by
  simp only [predictionPrefix, orderedProduct_succ, Module.End.mul_apply,
    predictionStageNat, hk, dite_true, predictionStage_apply]

/-- A query prediction is unchanged after its physical call. -/
theorem predictionPrefix_stable (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) (s : Fin N) (k : ℕ) (hsk : s.val≤k) (hk : k≤N) :
    predictionPrefix h L initial k (some s)=predictionPrefix h L initial s.val (some s) := by
  induction k, hsk using Nat.le_induction with
  | base => rfl
  | succ k hsk ih =>
    rw [predictionPrefix_succ h L initial k (by omega)]
    have ha : h.a s ⟨k,by omega⟩=0 := h.triangular s _ (by exact hsk)
    simpa only [bezout.History.predictionCoefficient, ha, zero_smul, sub_zero] using ih (by omega)

omit [Module ℝ E] in
private theorem sum_before_succ (k : ℕ) (hk : k<N) (f : Fin N → E) :
    (∑ j : Fin N, if j.val<k+1 then f j else 0)=
      (∑ j : Fin N, if j.val<k then f j else 0)+f ⟨k,hk⟩ := by
  have he (j : Fin N) : (if j.val<k+1 then f j else 0)=
      (if j.val<k then f j else 0)+(if j=⟨k,hk⟩ then f j else 0) := by
    by_cases hj : j.val<k
    · have hne : j≠⟨k,hk⟩ := by
        intro he
        have heval : j.val=k := congrArg Fin.val he
        omega
      simp [hj, show j.val<k+1 by omega, hne]
    · by_cases he : j=⟨k,hk⟩
      · subst j; simp
      · have hn : ¬j.val<k+1 := by
          intro hl
          apply he
          apply Fin.ext
          change j.val=k
          omega
        simp [hj, he, hn]
  simp_rw [he, Finset.sum_add_distrib]
  simp

/-- Exact physical prediction invariant for all time-dependent linear oracles. -/
theorem predictionPrefix_invariant (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) (k : ℕ) (hk : k≤N) (i : Option (Fin N)) :
    predictionPrefix h L initial k i=initial-
      ∑ j : Fin N, if j.val<k then h.predictionCoefficient i j •
        L j (predictionPrefix h L initial j.val (some j)) else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [predictionPrefix_succ h L initial k (by omega), ih (by omega), sum_before_succ k (by omega)]
    abel

/-- The final prediction slots satisfy the complete physical history equations. -/
theorem predictionPrefix_final (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) (i : Option (Fin N)) :
    predictionPrefix h L initial N i=initial-
      ∑ j : Fin N, h.predictionCoefficient i j • L j (predictionPrefix h L initial N (some j)) := by
  rw [predictionPrefix_invariant h L initial N le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [j.isLt, ite_true]
  rw [predictionPrefix_stable h L initial j N j.isLt.le le_rfl]

/-- The product prediction terminal is the actual causal oracle output.
Use: subsequent multilinear coefficients refer to physical executions, not an assumed transfer. -/
theorem predictionPrefix_output (h : bezout.History N) (L : Fin N → E →ₗ[ℝ] E)
    (initial : E) : predictionPrefix h L initial N none=h.oracleOutput initial (fun s v => L s v) := by
  let answers : Fin N → E := fun s => L s (predictionPrefix h L initial N (some s))
  have ha : answers=h.oracleAnswers initial (fun s v => L s v) := by
    apply h.oracleAnswers_unique initial (fun s v => L s v)
    intro s
    change L s (predictionPrefix h L initial N (some s))=L s (initial-∑ j, h.a s j • answers j)
    rw [predictionPrefix_final h L initial (some s)]
    rfl
  rw [predictionPrefix_final h L initial none]
  change initial-∑ j, h.b j • answers j=h.oracleOutput initial (fun s v => L s v)
  rw [ha]
  rfl

end
end bezout.Channel

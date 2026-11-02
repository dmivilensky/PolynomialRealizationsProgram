import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
Article: bezout, Equation `eq:competitor-masg` and incomplete final stages.
Use: an actual stage clock consumes one call at a time, with the prescribed
first-stage length and geometric later lengths. It stops at the exact budget.
Proof: the used count is strictly below its stage length, and completed-stage
lengths plus the current used count equal the elapsed number of calls.
-/

namespace bezout.Comparisons.Competitors.MASG
noncomputable section
open scoped BigOperators

/-- The literal first-stage budget and later geometric stage lengths. -/
def stageLength (N B k : ℕ) : ℕ := if k=1 then N/2 else 2^k*B

/-- The current stage number (starting at one) and already used calls in it. -/
structure StageClock where
  stage : ℕ
  used : ℕ

/-- Consume one call, advancing and resetting precisely at a completed stage. -/
def advance (N B : ℕ) (clock : StageClock) : StageClock :=
  if clock.used+1<stageLength N B clock.stage then
    ⟨clock.stage,clock.used+1⟩ else ⟨clock.stage+1,0⟩

/-- The actual per-call stage schedule, independent of the physical oracle stream. -/
def clock (N B : ℕ) : ℕ → StageClock
  | 0 => ⟨1,0⟩
  | n+1 => advance N B (clock N B n)

/-- Every stage actually entered has a positive prescribed length. -/
theorem stageLength_pos {N B k : ℕ} (hN : 2≤N) (hB : 0<B) (_hk : 1≤k) :
    0<stageLength N B k := by
  unfold stageLength
  split_ifs
  · omega
  · exact Nat.mul_pos (Nat.pow_pos (by omega)) hB

/-- The stage clock always names a live stage and a genuinely incomplete prefix. -/
theorem clock_valid (N B : ℕ) (hN : 2≤N) (hB : 0<B) (n : ℕ) :
    1≤(clock N B n).stage ∧ (clock N B n).used<stageLength N B (clock N B n).stage := by
  induction n with
  | zero => exact ⟨le_rfl,stageLength_pos hN hB le_rfl⟩
  | succ n ih =>
    rw [clock,advance]
    split_ifs with h
    · exact ⟨ih.1,h⟩
    · exact ⟨by dsimp; omega,stageLength_pos hN hB (by dsimp; omega)⟩

/-- The completed stages before k, excluding the current stage. -/
def completedLength (N B k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k-1), stageLength N B (j+1)

/-- Completing one whole stage adds exactly its prescribed budget. -/
theorem completedLength_succ (N B k : ℕ) (hk : 1≤k) :
    completedLength N B (k+1)=completedLength N B k+stageLength N B k := by
  unfold completedLength
  rw [Nat.add_sub_cancel]
  have he : k=(k-1)+1 := by omega
  conv_lhs => rw [he,Finset.sum_range_succ]
  simp only [show k-1+1=k by omega]

/-- The clock accounts for every call, including the unfinished final stage. -/
theorem clock_elapsed (N B : ℕ) (hN : 2≤N) (hB : 0<B) (n : ℕ) :
    completedLength N B (clock N B n).stage+(clock N B n).used=n := by
  induction n with
  | zero => simp [clock,completedLength]
  | succ n ih =>
    have hv := clock_valid N B hN hB n
    rw [clock,advance]
    split_ifs with h
    · change completedLength N B (clock N B n).stage+((clock N B n).used+1)=n+1
      omega
    · change completedLength N B ((clock N B n).stage+1)+0=n+1
      rw [completedLength_succ N B _ hv.1]
      omega

/-- The entire first stage has exactly floor(N/2) calls and no premature reset. -/
theorem clock_first_stage (N B : ℕ) (n : ℕ) (hn : n<N/2) : clock N B n=⟨1,n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [clock,ih (by omega),advance]
    rw [ite_eq_left (by simpa only [stageLength,ite_true] using hn)]

/-- The prescribed first stage ends by resetting into stage two. -/
theorem clock_first_boundary (N B : ℕ) (hN : 2≤N) : clock N B (N/2)=⟨2,0⟩ := by
  have hn : 0<N/2 := by omega
  have he : N/2=(N/2-1)+1 := by omega
  rw [he,clock,clock_first_stage N B _ (by omega),advance]
  rw [ite_eq_right (by simp only [stageLength,ite_true]; omega)]

/-- A reset occurs exactly when a call starts a newly entered stage. -/
theorem reset_iff_stage_change (N B n : ℕ) :
    (clock N B (n+1)).used=0 ↔ (clock N B (n+1)).stage≠(clock N B n).stage := by
  rw [clock,advance]
  split_ifs <;> simp

/-- The last physical call is a complete or partial prefix of its prescribed stage;
its elapsed budget is exactly N, even when the stage is stopped early. -/
theorem last_stage_budget (N B : ℕ) (hN : 2≤N) (hB : 0<B) :
    (clock N B (N-1)).used+1≤stageLength N B (clock N B (N-1)).stage ∧
      completedLength N B (clock N B (N-1)).stage+((clock N B (N-1)).used+1)=N := by
  have hv := clock_valid N B hN hB (N-1)
  have he := clock_elapsed N B hN hB (N-1)
  constructor <;> omega

end
end bezout.Comparisons.Competitors.MASG

import polyak.Functions.Transforms
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Article: Definition `def:slm`, the state in `def:rate`, and Appendix A.
Use: actual finite-memory stationary methods, without stability or coprimality
assumptions. Coefficients include their consistency identities and the nonzero
leading coefficient that makes the recursion explicit.
-/
namespace nesterov
noncomputable section
open scoped BigOperators

structure StationaryMethod where
  memory : ℕ
  memory_pos : 0 < memory
  queryCoeff : Fin memory → ℝ
  recurrenceCoeff : Fin (memory + 1) → ℝ
  query_sum : ∑ j, queryCoeff j = 1
  recurrence_sum : ∑ j, recurrenceCoeff j = 0
  leading_ne : recurrenceCoeff (Fin.last memory) ≠ 0

namespace StationaryMethod
variable (M : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual gradient query; latent and query coordinates are kept distinct. -/
def query (w : ℕ → E) (k : ℕ) : E := ∑ j, M.queryCoeff j • w (k + j)

/-- The literal stationary equation on every nonnegative time index. -/
def IsTrajectory (g : E → E) (w : ℕ → E) : Prop :=
  ∀ k, ∑ j, M.recurrenceCoeff j • w (k + j) = g (M.query w k)

/-- The Hilbert product norm of the complete memory state. -/
def stateNorm (w : ℕ → E) (k : ℕ) : ℝ :=
  Real.sqrt (∑ j : Fin M.memory, ‖w (k + j)‖ ^ 2)

/-- The query polynomial in the article's ascending-power convention. -/
def queryPolynomial : Polynomial ℝ := ∑ j : Fin M.memory, Polynomial.monomial j (M.queryCoeff j)

/-- The recursion polynomial in the same convention. -/
def recurrencePolynomial : Polynomial ℝ :=
  ∑ j : Fin (M.memory + 1), Polynomial.monomial j (M.recurrenceCoeff j)

@[simp] theorem query_zero (w : ℕ → E) : M.query w 0 = ∑ j, M.queryCoeff j • w j := by
  simp [query]

@[simp] theorem query_const (a : E) (k : ℕ) : M.query (fun _ => a) k = a := by
  simp only [query, ← Finset.sum_smul, M.query_sum, one_smul]

@[simp] theorem recurrence_const (a : E) (k : ℕ) :
    (∑ j : Fin (M.memory + 1), M.recurrenceCoeff j • (fun _ : ℕ => a) (k+j)) = 0 := by
  simp only [← Finset.sum_smul, M.recurrence_sum, zero_smul]

theorem query_shift (w : ℕ → E) (l k : ℕ) :
    M.query (fun i => w (l+i)) k = M.query w (l+k) := by
  simp [query, Nat.add_assoc]

theorem IsTrajectory.shift {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) (l : ℕ) : M.IsTrajectory g (fun i => w (l+i)) := by
  intro k
  simpa [query, Nat.add_assoc] using h (l+k)

omit [NormedSpace ℝ E] in
@[simp] theorem stateNorm_shift (w : ℕ → E) (l k : ℕ) :
    M.stateNorm (fun i => w (l+i)) k = M.stateNorm w (l+k) := by
  simp [stateNorm, Nat.add_assoc]

omit [NormedSpace ℝ E] in
theorem stateNorm_nonneg (w : ℕ → E) (k : ℕ) : 0 ≤ M.stateNorm w k := Real.sqrt_nonneg _

omit [NormedSpace ℝ E] in
theorem stateNorm_sq (w : ℕ → E) (k : ℕ) :
    M.stateNorm w k ^ 2 = ∑ j : Fin M.memory, ‖w (k+j)‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

omit [NormedSpace ℝ E] in
theorem norm_le_stateNorm (w : ℕ → E) (k : ℕ) (j : Fin M.memory) :
    ‖w (k+j)‖ ≤ M.stateNorm w k := by
  have hs := Finset.single_le_sum (fun (i : Fin M.memory) _ => sq_nonneg ‖w (k+i)‖)
    (Finset.mem_univ j)
  nlinarith [M.stateNorm_sq w k, M.stateNorm_nonneg w k, norm_nonneg (w (k+j))]

omit [NormedSpace ℝ E] in
theorem stateNorm_eq_zero_iff (w : ℕ → E) (k : ℕ) :
    M.stateNorm w k = 0 ↔ ∀ j : Fin M.memory, w (k+j) = 0 := by
  constructor
  · intro h j
    exact norm_eq_zero.mp (le_antisymm (h ▸ M.norm_le_stateNorm w k j) (norm_nonneg _))
  · intro h
    simp [stateNorm, h]

/-- Translation uses both coefficient consistency identities. -/
theorem query_sub_const (w : ℕ → E) (a : E) (k : ℕ) :
    M.query (fun i => w i-a) k = M.query w k-a := by
  simp only [query, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    M.query_sum, one_smul]

/-- Actual recentering of every trajectory at an arbitrary spatial point. -/
theorem IsTrajectory.center {g : E → E} {w : ℕ → E}
    (h : M.IsTrajectory g w) (a : E) :
    M.IsTrajectory (fun e => g (a+e)) (fun k => w k-a) := by
  intro k
  rw [M.query_sub_const]
  simp only [add_sub_cancel]
  simpa only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
    M.recurrence_sum, zero_smul, sub_zero] using h k

end StationaryMethod
end
end nesterov

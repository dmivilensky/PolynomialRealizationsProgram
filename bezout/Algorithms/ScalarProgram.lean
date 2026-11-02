import bezout.Algorithms.Registers
import chebyshev1.Chebyshev.Normalization

/-!
Article: bezout, Algorithms 1--2 (linear scalar preparation work).
Use: an exact-arithmetic RAM semantics for cached scalar straight-line programs.
Inputs, constants and cached reads cost no arithmetic operation; each real
addition, subtraction, multiplication or division costs one. Each node is
computed once in topological order and stored in its own scalar cell.
Proof: expression induction proves the evaluator's actual operation counter;
causality and prefix induction identify every cached cell with a target table.
-/

namespace bezout.Algorithms
noncomputable section
open scoped BigOperators

/-- Scalar arithmetic with named inputs and reads of earlier cached cells. -/
inductive ScalarExpr where
  | constant (value : ℝ)
  | input (index : ℕ)
  | read (index : ℕ)
  | add (left right : ScalarExpr)
  | sub (left right : ScalarExpr)
  | mul (left right : ScalarExpr)
  | div (left right : ScalarExpr)

namespace ScalarExpr

/-- Cached cells read by an arithmetic expression. -/
def reads : ScalarExpr → Finset ℕ
  | .constant _ => ∅
  | .input _ => ∅
  | .read j => {j}
  | .add e f | .sub e f | .mul e f | .div e f => e.reads ∪ f.reads

/-- Actual scalar evaluation and its arithmetic-operation counter. -/
def evalWithCost (inputs memory : ℕ → ℝ) : ScalarExpr → ℝ × ℕ
  | .constant c => (c,0)
  | .input j => (inputs j,0)
  | .read j => (memory j,0)
  | .add e f =>
      let a := e.evalWithCost inputs memory
      let b := f.evalWithCost inputs memory
      (a.1+b.1,a.2+b.2+1)
  | .sub e f =>
      let a := e.evalWithCost inputs memory
      let b := f.evalWithCost inputs memory
      (a.1-b.1,a.2+b.2+1)
  | .mul e f =>
      let a := e.evalWithCost inputs memory
      let b := f.evalWithCost inputs memory
      (a.1*b.1,a.2+b.2+1)
  | .div e f =>
      let a := e.evalWithCost inputs memory
      let b := f.evalWithCost inputs memory
      (a.1/b.1,a.2+b.2+1)

/-- The scalar value returned by the operation-counting evaluator. -/
def eval (inputs memory : ℕ → ℝ) (e : ScalarExpr) : ℝ := (e.evalWithCost inputs memory).1

/-- Number of arithmetic nodes actually executed by the expression evaluator. -/
def cost : ScalarExpr → ℕ
  | .constant _ | .input _ | .read _ => 0
  | .add e f | .sub e f | .mul e f | .div e f => e.cost+f.cost+1

/-- All AST nodes visited by the evaluator, including arithmetic operations,
cached reads, original input reads and literal constants. -/
def nodeCount : ScalarExpr → ℕ
  | .constant _ | .input _ | .read _ => 1
  | .add e f | .sub e f | .mul e f | .div e f => e.nodeCount+f.nodeCount+1

/-- A binary arithmetic tree has one more leaf than arithmetic nodes. Thus all
read and constant visits are bounded by the actual arithmetic count. -/
theorem nodeCount_eq (e : ScalarExpr) : e.nodeCount = 2*e.cost+1 := by
  induction e <;> simp_all only [nodeCount,cost] <;> omega

/-- The expression operation count is independent of the data, and equals the
counter produced by its actual arithmetic evaluation. -/
theorem evalWithCost_cost (inputs memory : ℕ → ℝ) (e : ScalarExpr) :
    (e.evalWithCost inputs memory).2 = e.cost := by
  induction e <;> simp_all [evalWithCost,cost]

/-- Agreement on the cells actually read suffices to identify expression values. -/
theorem eval_congr_reads (inputs memory memory' : ℕ → ℝ) (e : ScalarExpr)
    (hm : ∀ j, j ∈ e.reads → memory j = memory' j) :
    e.eval inputs memory = e.eval inputs memory' := by
  induction e with
  | constant c => rfl
  | input j => rfl
  | read j => exact hm j (by simp [reads])
  | add e f he hf | sub e f he hf | mul e f he hf | div e f he hf =>
    have he' := he (fun j hj => hm j (Finset.mem_union_left _ hj))
    have hf' := hf (fun j hj => hm j (Finset.mem_union_right _ hj))
    simp only [eval,evalWithCost] at he' hf' ⊢
    rw [he',hf']

/-- Every real division actually evaluated by the expression has a nonzero
denominator. Use: rules out total-field defaults in concrete scalar preparation. -/
def Defined (inputs memory : ℕ → ℝ) : ScalarExpr → Prop
  | .constant _ | .input _ | .read _ => True
  | .add e f | .sub e f | .mul e f => e.Defined inputs memory ∧ f.Defined inputs memory
  | .div e f => e.Defined inputs memory ∧ f.Defined inputs memory ∧ f.eval inputs memory ≠ 0

/-- Division validity depends only on cached cells actually read by the expression. -/
theorem defined_congr_reads (inputs memory memory' : ℕ → ℝ) (e : ScalarExpr)
    (hm : ∀ j, j ∈ e.reads → memory j = memory' j) :
    e.Defined inputs memory ↔ e.Defined inputs memory' := by
  induction e with
  | constant c => rfl
  | input j => rfl
  | read j => rfl
  | add e f he hf | sub e f he hf | mul e f he hf =>
    exact and_congr (he (fun j hj => hm j (Finset.mem_union_left _ hj)))
      (hf (fun j hj => hm j (Finset.mem_union_right _ hj)))
  | div e f he hf =>
    have he' := he (fun j hj => hm j (Finset.mem_union_left _ hj))
    have hf' := hf (fun j hj => hm j (Finset.mem_union_right _ hj))
    have hv := f.eval_congr_reads inputs memory memory'
      (fun j hj => hm j (Finset.mem_union_right _ hj))
    exact and_congr he' (and_congr hf' (by rw [hv]))

/-- Literal scalar leaves return their value without arithmetic. -/
@[simp] theorem eval_constant (inputs memory : ℕ → ℝ) (c : ℝ) :
    (.constant c : ScalarExpr).eval inputs memory = c := rfl
/-- Input leaves read the given scalar input table. -/
@[simp] theorem eval_input (inputs memory : ℕ → ℝ) (j : ℕ) :
    (.input j : ScalarExpr).eval inputs memory = inputs j := rfl
/-- Cached leaves read their prescribed scalar cell. -/
@[simp] theorem eval_read (inputs memory : ℕ → ℝ) (j : ℕ) :
    (.read j : ScalarExpr).eval inputs memory = memory j := rfl
/-- The counted addition returns the sum of its operand values. -/
@[simp] theorem eval_add (inputs memory : ℕ → ℝ) (e f : ScalarExpr) :
    (ScalarExpr.add e f).eval inputs memory = e.eval inputs memory+f.eval inputs memory := rfl
/-- The counted subtraction returns the difference of its operand values. -/
@[simp] theorem eval_sub (inputs memory : ℕ → ℝ) (e f : ScalarExpr) :
    (ScalarExpr.sub e f).eval inputs memory = e.eval inputs memory-f.eval inputs memory := rfl
/-- The counted multiplication returns the product of its operand values. -/
@[simp] theorem eval_mul (inputs memory : ℕ → ℝ) (e f : ScalarExpr) :
    (ScalarExpr.mul e f).eval inputs memory = e.eval inputs memory*f.eval inputs memory := rfl
/-- The counted division returns the quotient of its operand values. -/
@[simp] theorem eval_div (inputs memory : ℕ → ℝ) (e f : ScalarExpr) :
    (ScalarExpr.div e f).eval inputs memory = e.eval inputs memory/f.eval inputs memory := rfl

end ScalarExpr

/-- A topologically ordered scalar single-assignment program with M cached cells. -/
structure ScalarProgram (M : ℕ) where
  node : Fin M → ScalarExpr
  causal : ∀ s j, j ∈ (node s).reads → j<s.val

/-- The scalar RAM stores exactly M cached values and an arithmetic counter. -/
structure ScalarState (M : ℕ) where
  values : Fin M → ℝ
  cost : ℕ

namespace ScalarProgram
variable {M : ℕ}

/-- Read a finite cache, returning zero at addresses outside its allocated cells.
Causality guarantees that actual expression reads always address earlier cells. -/
def extend (values : Fin M → ℝ) (j : ℕ) : ℝ := if hj : j<M then values ⟨j,hj⟩ else 0

/-- One topological pass, caching every node after computing it exactly once. -/
def runPrefix (program : ScalarProgram M) (inputs : ℕ → ℝ) : ℕ → ScalarState M
  | 0 => ⟨fun _ => 0,0⟩
  | k+1 =>
      let old := program.runPrefix inputs k
      if hk : k<M then
        let result := (program.node ⟨k,hk⟩).evalWithCost inputs (extend old.values)
        ⟨Function.update old.values ⟨k,hk⟩ result.1, old.cost+result.2⟩
      else old

/-- Execute the complete cached scalar preparation. -/
def run (program : ScalarProgram M) (inputs : ℕ → ℝ) : ScalarState M :=
  program.runPrefix inputs M

/-- Prefix correctness from the local exact equations of a target scalar table. -/
theorem runPrefix_correct (program : ScalarProgram M) (inputs : ℕ → ℝ)
    (values : Fin M → ℝ)
    (hv : ∀ s, (program.node s).eval inputs (extend values) = values s)
    (k : ℕ) (hk : k≤M) (s : Fin M) (hs : s.val<k) :
    (program.runPrefix inputs k).values s = values s := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    have hkM : k<M := by omega
    have he : (program.node ⟨k,hkM⟩).eval inputs
        (extend (program.runPrefix inputs k).values) = values ⟨k,hkM⟩ := by
      rw [← hv ⟨k,hkM⟩]
      apply ScalarExpr.eval_congr_reads
      intro j hj
      have hjk : j<k := program.causal ⟨k,hkM⟩ j hj
      simp only [extend, dite_eq_left (show j<M by omega)]
      exact ih (by omega) ⟨j,by omega⟩ hjk
    simp only [runPrefix, dite_eq_left hkM]
    by_cases hsk : s=⟨k,hkM⟩
    · subst s
      simpa only [Function.update_self, ScalarExpr.eval] using he
    · rw [Function.update_of_ne hsk]
      exact ih (by omega) s (by
        have hne : s.val≠k := fun he => hsk (Fin.ext he)
        omega)

/-- A nodewise target table is exactly the table returned by the actual cached run. -/
theorem run_correct (program : ScalarProgram M) (inputs : ℕ → ℝ) (values : Fin M → ℝ)
    (hv : ∀ s, (program.node s).eval inputs (extend values) = values s) :
    (program.run inputs).values = values := by
  funext s
  exact program.runPrefix_correct inputs values hv M le_rfl s s.isLt

/-- Convenient natural-address correctness, using any target value outside the cache. -/
theorem run_correct_nat (program : ScalarProgram M) (inputs values : ℕ → ℝ)
    (hv : ∀ s, (program.node s).eval inputs values = values s.val) :
    (program.run inputs).values = fun s => values s.val := by
  apply program.run_correct
  intro s
  rw [← hv s]
  apply ScalarExpr.eval_congr_reads
  intro j hj
  have hjM : j<M := (program.causal s j hj).trans s.isLt
  simp only [extend, dite_eq_left hjM]

/-- Nodewise nonzero denominators are valid at the moment each actual cached
node is evaluated, not merely in a separate closed-form specification. -/
theorem runPrefix_defined (program : ScalarProgram M) (inputs : ℕ → ℝ)
    (values : Fin M → ℝ)
    (hv : ∀ s, (program.node s).eval inputs (extend values) = values s)
    (hd : ∀ s, (program.node s).Defined inputs (extend values)) (s : Fin M) :
    (program.node s).Defined inputs (extend (program.runPrefix inputs s.val).values) := by
  apply (ScalarExpr.defined_congr_reads inputs _ (extend values) (program.node s) ?_).mpr (hd s)
  intro j hj
  have hjs : j<s.val := program.causal s j hj
  have hjM : j<M := hjs.trans s.isLt
  simp only [extend, dite_eq_left hjM]
  exact program.runPrefix_correct inputs values hv s.val (Nat.le_of_lt s.isLt) ⟨j,hjM⟩ hjs

/-- Natural-address division certificates transfer to the actual cached execution. -/
theorem runPrefix_defined_nat (program : ScalarProgram M) (inputs values : ℕ → ℝ)
    (hv : ∀ s, (program.node s).eval inputs values = values s.val)
    (hd : ∀ s, (program.node s).Defined inputs values) (s : Fin M) :
    (program.node s).Defined inputs (extend (program.runPrefix inputs s.val).values) := by
  let v : Fin M → ℝ := fun j => values j.val
  have ha (j : Fin M) (i : ℕ) (hi : i ∈ (program.node j).reads) : extend v i = values i := by
    have hiM : i<M := (program.causal j i hi).trans j.isLt
    simp only [extend, dite_eq_left hiM, v]
  apply program.runPrefix_defined inputs v
  · intro j
    change (program.node j).eval inputs (extend v) = values j.val
    rw [← hv j]
    exact ScalarExpr.eval_congr_reads inputs _ values _ (ha j)
  · intro j
    exact (ScalarExpr.defined_congr_reads inputs _ values _ (ha j)).mpr (hd j)

/-- Extend the program's arithmetic costs by zero outside the actual node range. -/
def nodeCost (program : ScalarProgram M) (j : ℕ) : ℕ :=
  if hj : j<M then (program.node ⟨j,hj⟩).cost else 0

/-- Every prefix counter counts exactly the arithmetic nodes actually evaluated. -/
theorem runPrefix_cost (program : ScalarProgram M) (inputs : ℕ → ℝ) (k : ℕ) :
    (program.runPrefix inputs k).cost = ∑ j ∈ Finset.range k, program.nodeCost j := by
  induction k with
  | zero => simp [runPrefix]
  | succ k ih =>
    rw [runPrefix, Finset.sum_range_succ]
    by_cases hk : k<M
    · simp only [dite_eq_left hk, ScalarExpr.evalWithCost_cost, ih, nodeCost]
    · simp only [dite_eq_right hk, ih, nodeCost, add_zero]

/-- The actual operation counter is the sum of the node arithmetic costs. -/
theorem run_cost (program : ScalarProgram M) (inputs : ℕ → ℝ) :
    (program.run inputs).cost = ∑ s : Fin M, (program.node s).cost := by
  rw [run, runPrefix_cost, ← Fin.sum_univ_eq_sum_range (fun j => program.nodeCost j) M]
  simp only [nodeCost, Fin.is_lt, dite_true]

/-- The total AST traversal work counts every arithmetic node and every leaf
visit of every expression actually evaluated once by the cached program. -/
theorem sum_nodeCount (program : ScalarProgram M) (inputs : ℕ → ℝ) :
    (∑ s : Fin M, (program.node s).nodeCount) = 2*(program.run inputs).cost+M := by
  simp_rw [ScalarExpr.nodeCount_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← program.run_cost inputs]
  simp

/-- The cached scalar state allocates exactly M scalar cells. -/
theorem scalar_cells (_program : ScalarProgram M) : Fintype.card (Fin M) = M :=
  Fintype.card_fin M

end ScalarProgram
/-- The interval header computes Delta and eta from the original inputs mu,L.
Use: derived spectral parameters are counted rather than supplied for free. -/
def intervalHeader : ScalarProgram 2 where
  node s := if s.val=0 then .sub (.input 1) (.input 0) else
    .div (.add (.input 1) (.input 0)) (.read 0)
  causal s j hj := by
    by_cases hs : s.val=0
    · simp [hs, ScalarExpr.reads] at hj
    · simp only [hs, ite_false, ScalarExpr.reads, Finset.empty_union,
        Finset.mem_singleton] at hj
      subst j
      omega

/-- The two original interval inputs, before any derived arithmetic. -/
def intervalInputs (I : chebyshev1.SpectralInterval) (j : ℕ) : ℝ :=
  if j=0 then I.mu else if j=1 then I.L else 0

/-- Expected header scalar values: Delta followed by eta. -/
def intervalHeaderValue (I : chebyshev1.SpectralInterval) (j : ℕ) : ℝ :=
  if j=0 then I.delta else I.eta

/-- Each header expression gives its exact prepared spectral parameter. -/
theorem intervalHeader_equation (I : chebyshev1.SpectralInterval) (s : Fin 2) :
    (intervalHeader.node s).eval (intervalInputs I) (intervalHeaderValue I) =
      intervalHeaderValue I s.val := by
  fin_cases s <;>
    simp [intervalHeader, intervalInputs, intervalHeaderValue,
      chebyshev1.SpectralInterval.delta, chebyshev1.SpectralInterval.eta]

/-- The actually executed header caches precisely Delta and eta. -/
theorem intervalHeader_values (I : chebyshev1.SpectralInterval) :
    (intervalHeader.run (intervalInputs I)).values = fun s => intervalHeaderValue I s.val :=
  intervalHeader.run_correct_nat _ _ (intervalHeader_equation I)

/-- Computing the original interval's two derived parameters takes exactly three
real arithmetic operations in the actual cached evaluator. -/
theorem intervalHeader_cost (inputs : ℕ → ℝ) : (intervalHeader.run inputs).cost = 3 := by
  rw [ScalarProgram.run_cost]
  simp [intervalHeader, Fin.sum_univ_succ, ScalarExpr.cost]

/-- The sole header division uses the strictly positive Delta. -/
theorem intervalHeader_defined (I : chebyshev1.SpectralInterval) (s : Fin 2) :
    (intervalHeader.node s).Defined (intervalInputs I)
      (ScalarProgram.extend (intervalHeader.runPrefix (intervalInputs I) s.val).values) := by
  apply intervalHeader.runPrefix_defined_nat _ _ (intervalHeader_equation I)
  intro j
  fin_cases j <;> simp [intervalHeader, ScalarExpr.Defined, intervalHeaderValue,
    ne_of_gt I.delta_pos]

end
end bezout.Algorithms

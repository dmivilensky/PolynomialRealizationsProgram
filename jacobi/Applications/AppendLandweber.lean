import chebyshev1.TwoTerm.Quadratic
import chebyshev1.Realization.Gain

/-!
Article: jacobi, Proposition 1.2.
Appending literal Landweber steps is performed within the earlier
article's genuine one-query TwoTerm realization. Its causal products
and insertion kernels therefore remain actual operator derivatives.
Use: BlockKernel and UniformBlockGain evaluate the full block gain.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original two-term stage of length m followed by literal unit-step Landweber iterations.
Use: its true ordered products and first-variation kernels describe the terminal-equivalent block from the article.
Article: jacobi, Proposition 1.2.
-/
def appendLandweber (S:TwoTerm) (m:ℕ) : TwoTerm where
  a s := if s<m then S.a s else 1
  b s := if s<m then S.b s else 0
  gamma s := if s<m then S.gamma s else 1

/-- Every actual step before the stage boundary equals the original one-query iteration step.
Use: append_prefix and the stage insertion formula preserve every original Jacobi recurrence and query exactly.
Article: jacobi, Proposition 1.2.
Proof: the original step lies in the first branch of all three genuine TwoTerm coefficient fields. -/
theorem append_scalarStep_before (S:TwoTerm) {m s:ℕ} (hs:s<m) (l:ℝ) :
    (appendLandweber S m).realization.scalarStep s l=S.realization.scalarStep s l := by
  cases s with
  | zero => simp [TwoTerm.scalarStep_zero,appendLandweber,hs]
  | succ s => simp [TwoTerm.scalarStep_succ,appendLandweber,hs]

/-- Every appended genuine step is the literal Landweber map on the current error and a memory shift.
Use: append_tail_after evaluates its true causal propagation even at a zero-length Jacobi stage.
Article: jacobi, Proposition 1.2.
Proof: the three coefficient fields are one, zero and one after the boundary, including the separately specified original time-zero step. -/
theorem append_scalarStep_after (S:TwoTerm) {m s:ℕ} (hs:m≤s) (l:ℝ) :
    (appendLandweber S m).realization.scalarStep s l=!![1-l,0;1,0] := by
  cases s with
  | zero => simp [TwoTerm.scalarStep_zero,appendLandweber,not_lt.mpr hs]
  | succ s => simp [TwoTerm.scalarStep_succ,appendLandweber,not_lt.mpr hs]

/-- All genuine causal products confined to the first stage agree with the original products.
Use: prefix transfer and first-stage insertions are those of the actual Jacobi method.
Article: jacobi, Proposition 1.2.
Proof: every factor index is strictly below the original stage boundary. Apply the earlier causal-product congruence theorem. -/
theorem append_prefix (S:TwoTerm) {m r n:ℕ} (hn:r+n≤m) (l:ℝ) :
    orderedProduct (fun i => (appendLandweber S m).realization.scalarStep (r+i) l) n=
      orderedProduct (fun i => S.realization.scalarStep (r+i) l) n := by
  apply orderedProduct_congr
  intro i hi
  exact append_scalarStep_before S (by omega) l

/-- The actual first row of every appended Landweber tail is its true scalar power.
Use: proves both stage and Landweber insertion formulas with their original empty-tail convention.
Article: jacobi, Proposition 1.2.
Proof: the original zero-length product is the identity. Each genuine later step multiplies its first row by 1-lambda and has zero upper-right entry. -/
theorem append_tail_after (S:TwoTerm) {m r:ℕ} (hr:m≤r) (d:ℕ) (l:ℝ) :
    let M := orderedProduct (fun i => (appendLandweber S m).realization.scalarStep (r+i) l) d
    M 0 0=(1-l)^d ∧ M 0 1=0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    dsimp only at ih ⊢
    rw [orderedProduct_succ,append_scalarStep_after S (by omega)]
    simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,ih.1,ih.2,pow_succ]
    constructor <;> ring

/-- A genuine tail crossing the stage boundary is exactly its original Jacobi-stage tail multiplied by the appended Landweber factor.
Use: BlockKernel computes the original first-stage Hessian insertions at the full terminal horizon.
Article: jacobi, Theorem 5.1.
Proof: split the original causal product at the actual stage boundary. Its later first row is the true Landweber power, and its earlier product is exactly the unchanged stage product. -/
theorem append_tail_stage (S:TwoTerm) {m r:ℕ} (hr:r≤m) (d:ℕ) (l:ℝ) :
    orderedProduct (fun i => (appendLandweber S m).realization.scalarStep (r+i) l) (m-r+d) 0 0=
      (1-l)^d*orderedProduct (fun i => S.realization.scalarStep (r+i) l) (m-r) 0 0 := by
  -- The split uses the exact original causal order: later Landweber factors multiply on the left.
  rw [orderedProduct_add]
  simp only [← Nat.add_assoc]
  have hp := append_tail_after S (m := m) (r := r+(m-r)) (by omega) d l
  dsimp only at hp
  simp only [Matrix.mul_apply,Fin.sum_univ_two,hp.1,hp.2,zero_mul,add_zero]
  rw [append_prefix S (by omega)]

/-- The full original appended realization has exactly its stage residual times the true Landweber polynomial factor.
Use: proves terminal equivalence while preserving one actual operator application per step.
Article: jacobi, Proposition 1.2.
Proof: the original TwoTerm readout selects the first matrix entry; apply the exact causal split at the stage boundary. -/
theorem append_transfer (S:TwoTerm) (m d:ℕ) (l:ℝ) :
    (appendLandweber S m).realization.scalarTransfer (m+d) l=(1-l)^d*S.realization.scalarTransfer m l := by
  simpa only [Realization.scalarTransfer,TwoTerm.scalarContract,Nat.zero_add,Nat.sub_zero] using
    append_tail_stage S (r := 0) (Nat.zero_le m) d l

end
end jacobi.Applications

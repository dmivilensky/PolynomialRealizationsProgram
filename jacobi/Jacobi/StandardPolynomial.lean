import jacobi.Jacobi.GeneralRecurrence
import jacobi.Jacobi.Nodes
import jacobi.Finite.PolynomialIdentification

/-!
Identification of the concrete standard chain with the actual Jacobi fibre.
The endpoint-normalized polynomial recurrence and the existing continuant
determinant theorem identify every prefix, including the terminal degree.
Use: StandardJacobi applies the Green and flow theorems to a genuine
standard realization, with its exact characteristic polynomial proved.
Article: jacobi, Theorem 5.4.
Article role: construction of the actual standard Jacobi matrix in its polynomial fibre.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial chebyshev1 chebyshev2 jacobi.Finite
set_option backward.isDefEq.respectTransparency false

/-- The positive factor making the endpoint-normalized polynomial monic.
Article: jacobi, Theorem 5.4.
-/
def standardNormalization (a b : ℝ) (n : ℕ) : ℝ :=
  ∏ i∈Finset.range n,standardForward a b i

/-- Each new monic factor is the true next forward recurrence coefficient.
Article: jacobi, Theorem 5.4.
-/
theorem standardNormalization_succ (a b : ℝ) (n : ℕ) :
    standardNormalization a b (n+1)=standardNormalization a b n*standardForward a b n :=
  Finset.prod_range_succ _ _

/-- No monic normalization factor vanishes throughout the full parameter range.
Article: jacobi, Theorem 5.4.
-/
theorem standardNormalization_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) :
    0<standardNormalization a b n :=
  Finset.prod_pos (fun _ _ => standardForward_pos ha hb _)

/-- The actual finite chain diagonal is the endpoint recurrence diagonal.
Article: jacobi, Theorem 5.4.
-/
theorem standardChain_diagonal {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {N i : ℕ} (hi : i<N) :
    (standardChain a b ha hb N).data.b i=1-standardForward a b i-standardBackward a b i :=
  ite_eq_left hi

/-- Interior squared links are the adjacent positive recurrence products.
Article: jacobi, Theorem 5.4.
-/
theorem standardChain_coupling {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {N i : ℕ} (hi : 0 < i) (hiN : i<N) :
    (standardChain a b ha hb N).data.aSq i=standardForward a b (i-1)*standardBackward a b i :=
  ite_eq_left ⟨hi,hiN⟩

/-- Every actual standard-chain prefix is the same genuine Jacobi
polynomial after the exact affine coordinate change and monic scaling.
Article: jacobi, Theorem 5.4.
-/
theorem standardChain_leading_eval {a b : ℝ} (ha : -1<a) (hb : -1<b)
    (N n : ℕ) (hn : n≤N) (x : ℝ) :
    ((standardChain a b ha hb N).data.leading n).eval x=
      standardNormalization a b n*(shiftedPolynomial a b n).eval ((1-x)/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.leading,JacobiData.block,standardNormalization,shiftedPolynomial_initial]
  | one =>
    have hr := congrArg (fun p : ℝ[X] => p.eval ((1-x)/2))
      (standard_polynomial_recurrence ha hb 0)
    simp only [eval_mul,eval_sub,eval_one,eval_ofNat,eval_X,eval_C,
      shiftedPolynomial_initial,eval_one,standardBackward,ite_true,sub_zero] at hr
    rw [JacobiData.leading,JacobiData.block,eval_sub,eval_X,eval_C,
      standardChain_diagonal ha hb (show 0<N by omega),standardNormalization_succ]
    simp only [standardNormalization,Finset.range_zero,Finset.prod_empty,one_mul,
      standardBackward,ite_true,sub_zero]
    linear_combination -hr
  | more n h0 h1 =>
    have hr := congrArg (fun p : ℝ[X] => p.eval ((1-x)/2))
      (standard_polynomial_recurrence ha hb (n+1))
    simp only [eval_mul,eval_sub,eval_one,eval_ofNat,eval_X,eval_C,Nat.add_sub_cancel] at hr
    rw [JacobiData.leading_add_two,eval_sub,eval_mul,eval_sub,eval_X,eval_C,
      eval_mul,eval_C,h0 (by omega),h1 (by omega),
      standardChain_diagonal ha hb (show n+1<N by omega),
      standardChain_coupling ha hb (show 0<n+1 by omega) (show n+1<N by omega),
      Nat.add_sub_cancel,standardNormalization_succ,standardNormalization_succ]
    simp only [standardNormalization_succ]
    linear_combination -standardNormalization a b n*standardForward a b n*hr

/-- The standard chain has exactly the prescribed complete Jacobi
characteristic polynomial. The proof uses every actual root, monicity
and the exact degree, rather than merely a limiting spectral match.
Article: jacobi, Theorem 5.4.
-/
theorem standardChain_charpoly {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    (standardChain a b ha hb N).matrix.charpoly=(nodes a b ha hb N).polynomial := by
  apply (nodes a b ha hb N).eq_polynomial (Matrix.charpoly_monic _)
    (by simp only [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin])
  intro i
  rw [Jacobi.matrix,← JacobiData.block_eq_charpoly _ (standardChain a b ha hb N).coupling_nonneg]
  change ((standardChain a b ha hb N).data.leading N).eval _=0
  rw [standardChain_leading_eval ha hb N N le_rfl]
  have hx : (1-(nodes a b ha hb N).value i)/2=shiftedRoots a b ha hb N i := by
    dsimp [nodes]
    ring
  rw [hx,(mem_roots (shiftedPolynomial_ne_zero ha hb N)).mp
    (shiftedRoots_properties ha hb i).1,mul_zero]

/-- The constructed standard matrix is a genuine member of the full
irreducible Jacobi fibre for every dimension and every a,b>-1.
Article: jacobi, Theorem 5.4.
-/
theorem standardChain_inFiber {a b : ℝ} (ha : -1<a) (hb : -1<b) (N : ℕ) :
    InFiber (standardChain a b ha hb N) (nodes a b ha hb N).polynomial :=
  ⟨standardChain_irreducible ha hb N,standardChain_charpoly ha hb N⟩

end
end jacobi.Jacobi

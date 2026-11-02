import jacobi.Jacobi.OrthogonalRoots
import jacobi.Finite.Fiber
import Mathlib.Data.Finset.Sort

/-!
Article: jacobi, Lemma 1.3.
The actual simple roots of the actual Jacobi polynomial are sorted by the
community finite order isomorphism. Their affine image is packaged in the
existing arbitrary-fibre Nodes type, reusing the full finite realization
and persymmetry machinery without a parallel special-case matrix theory.
Source: the proved real orthogonal-polynomial zero theorem and Finset.orderEmbOfFin.
Use: supplies a canonical complete finite zero list for ordered Mehler--Heine transfer and the article's matrix fibre.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Set
set_option backward.isDefEq.respectTransparency false

/-- The genuine shifted Jacobi zeros, in increasing order, as the community finite order embedding.
Use: supplies a canonical complete finite zero list for ordered Mehler--Heine transfer and the article's matrix fibre.
Article: jacobi, Theorem 5.1.
-/
def shiftedRoots (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : Fin n ↪o ℝ := by
  classical
  let p := shiftedPolynomial a b n
  have hp := shiftedPolynomial_roots ha hb n
  exact p.roots.toFinset.orderEmbOfFin ((Multiset.toFinset_card_of_nodup hp.2.1).trans hp.1)

/-- Every canonically ordered shifted Jacobi zero belongs to the actual root multiset and lies strictly between zero and one.
Use: gives the actual endpoint separation and positivity needed by every finite spectral reciprocal.
Article: jacobi, Proposition A.1.
Proof: the community sorted embedding takes values in the original
root finset, and the proved complete root theorem gives the interior bounds. -/
theorem shiftedRoots_properties {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    shiftedRoots a b ha hb n i∈(shiftedPolynomial a b n).roots ∧
      shiftedRoots a b ha hb n i∈Ioo (0:ℝ) 1 := by
  classical
  have hmem : shiftedRoots a b ha hb n i∈(shiftedPolynomial a b n).roots.toFinset :=
    Finset.orderEmbOfFin_mem _ _ i
  have hm : shiftedRoots a b ha hb n i∈(shiftedPolynomial a b n).roots := Multiset.mem_toFinset.mp hmem
  exact ⟨hm,(shiftedPolynomial_roots ha hb n).2.2.1 _ hm⟩

/-- The canonical shifted-zero list contains every actual real Jacobi zero and only those zeros.
Use: identifies arbitrary finite zero candidates with their exact canonical source index.
Article: jacobi, Lemma 1.3.
Proof: the actual nonzero polynomial's roots are exactly its vanishing
evaluations, and the community order embedding has precisely the original finite root set as its range. -/
theorem shiftedRoots_exhaustive {a b : ℝ} (ha : -1<a) (hb : -1<b) (n : ℕ) (x : ℝ) :
    (shiftedPolynomial a b n).eval x=0 ↔ ∃ i:Fin n,shiftedRoots a b ha hb n i=x := by
  classical
  change (shiftedPolynomial a b n).IsRoot x ↔ ∃ i:Fin n,shiftedRoots a b ha hb n i=x
  rw [← mem_roots (shiftedPolynomial_ne_zero ha hb n),← Multiset.mem_toFinset]
  change x∈(shiftedPolynomial a b n).roots.toFinset ↔ x∈range (shiftedRoots a b ha hb n)
  rw [shiftedRoots,Finset.range_orderEmbOfFin]
  rfl

/-- The literal finite Jacobi nodes in the article's decreasing order.
Use: connects the special-function polynomial to the existing arbitrary polynomial fibre and packing theory.
Article: jacobi, Proposition B.1.
-/
def nodes (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) : jacobi.Finite.Nodes n where
  value i := 1-2*shiftedRoots a b ha hb n i
  strictAnti := by
    intro i j hij
    have h := (shiftedRoots a b ha hb n).strictMono hij
    linarith
  interval i := by
    obtain ⟨_,ht⟩ := shiftedRoots_properties ha hb i
    constructor <;> linarith [ht.1,ht.2]

/-- Every ordered finite Jacobi node is a genuine zero of the original terminating complex hypergeometric polynomial.
Use: the article's original polynomial and the earlier finite-fibre construction have exactly the same node data.
Article: jacobi, Lemma 1.3.
Proof: the sorted shifted root is an actual polynomial root. Its affine
coordinate evaluates to the original real Jacobi function, whose reality
identifies vanishing of the real restriction with the original complex value. -/
theorem nodes_are_zeros {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (i : Fin n) :
    normalized (a:ℂ) (b:ℂ) n ((nodes a b ha hb n).value i:ℂ)=0 := by
  apply (realNormalized_zero_iff _ _ _ _).mp
  change realNormalized a b n (1-2*shiftedRoots a b ha hb n i)=0
  rw [← shiftedPolynomial_eval]
  exact (mem_roots (shiftedPolynomial_ne_zero ha hb n)).mp (shiftedRoots_properties ha hb i).1

end
end jacobi.Jacobi

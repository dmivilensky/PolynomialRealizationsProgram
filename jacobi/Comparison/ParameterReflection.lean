import jacobi.Comparison.Model
import jacobi.Finite.AlternatingConjugation
import jacobi.Jacobi.OrderedReflection
import chebyshev2.Finite.MatrixExt

/-!
Article: jacobi, Theorem C.5.
The genuine unique persymmetric target matrices with exchanged endpoint
parameters are exact alternating-sign spectral reflections. This reuses
the full actual Jacobi node reflection and the existing finite fibre
uniqueness, without an assumed matrix-entry formula for the candidate.
Use: targetChain_swap identifies the original reflected target by the already proved complete persymmetric fibre uniqueness.
-/
namespace jacobi.Comparison
noncomputable section
open Real Matrix Polynomial jacobi.Finite chebyshev2

/-- The original genuine target reflection belongs to the actual full
Jacobi fibre with exchanged endpoint parameters.
Use: targetChain_swap identifies the original reflected target by the
already proved complete persymmetric fibre uniqueness.
Article: jacobi, Theorem C.5.
Proof: evaluate the original reflected characteristic polynomial,
insert its actual complete Jacobi-node product, move the exact sign
inside the finite product, and reverse the genuine original node order. -/
theorem targetChain_reflect_charpoly (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (reflect (targetChain a b ha hb n)).matrix.charpoly=(jacobi.Jacobi.nodes b a hb ha (n+1)).polynomial := by
  -- The equality retains all genuine roots with their original multiplicities.
  apply Polynomial.funext
  intro x
  rw [reflect_charpoly_eval,(targetChain_inFiber a b ha hb n).2]
  simp only [Nodes.polynomial,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  rw [show (-1:ℝ)^(n+1)=∏_i:Fin (n+1),(-1:ℝ) by simp,← Finset.prod_mul_distrib]
  calc
    (∏i:Fin (n+1),(-1:ℝ)*(-x-(jacobi.Jacobi.nodes a b ha hb (n+1)).value i))=
      ∏i:Fin (n+1),(x+(jacobi.Jacobi.nodes a b ha hb (n+1)).value i) :=
        Finset.prod_congr rfl (fun _ _ => by ring)
    _=∏i:Fin (n+1),(x+(jacobi.Jacobi.nodes a b ha hb (n+1)).value i.rev) :=
      (Equiv.prod_comp Fin.revPerm _).symm
    _=_ := by simp only [jacobi.Jacobi.nodes_reflection ha hb,sub_eq_add_neg]

/-- The actual original target is fixed by the genuine finite physical
reversal, with its full canonical coefficient tails retained.
Use: targetChain_swap discharges physical persymmetry of the genuine
reflected candidate before applying original fibre uniqueness.
Article: jacobi, Theorem C.5.
Proof: the earlier exact matrix persymmetry and the existing injectivity
of the canonical finite Jacobi matrix representation give actual equality. -/
theorem targetChain_reverse (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    reverse (targetChain a b ha hb n)=targetChain a b ha hb n := by
  apply Jacobi.matrix_injective
  rw [reverse_matrix,targetChain_persymmetric]

/-- Swapping the original endpoint parameters gives exactly the
actual positive-coupling spectral reflection of the target chain.
Use: targetChain_swap_matrix and the actual complex resolvent reflection
transfer every right-edge statement of D to its original left edge.
Article: jacobi, Theorem C.5.
Proof: the genuine reflected candidate has the proved swapped original
polynomial, positive couplings and true physical persymmetry. Complete
uniqueness in that same original fibre identifies the unchanged target. -/
theorem targetChain_swap (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    targetChain b a hb ha n=reflect (targetChain a b ha hb n) := by
  -- Both exact original candidates lie in the same genuine swapped fibre.
  let S := jacobi.Jacobi.nodes b a hb ha (n+1)
  let J : Fiber (n+1) S.polynomial := ⟨reflect (targetChain a b ha hb n),
    affine_irreducible (targetChain_inFiber a b ha hb n).1 (by norm_num) 0,
    targetChain_reflect_charpoly a b ha hb n⟩
  let K : Fiber (n+1) S.polynomial := ⟨targetChain b a hb ha n,targetChain_inFiber b a hb ha n⟩
  have he : K=J := (exists_unique_persymmetric S).unique (targetChain_persymmetric b a hb ha n)
    (reflect_persymmetric (targetChain_reverse a b ha hb n))
  exact congrArg Subtype.val he

/-- The original target parameter swap is the exact printed physical
alternating-sign matrix conjugation.
Use: the genuine complex resolvent reflection proves all left-edge
conclusions of Theorem C.5 from the same verified right-edge results.
Article: jacobi, Theorem C.5.
Proof: the actual positive-coupling reflection is already proved equal
to minus the same original alternating diagonal conjugation. -/
theorem targetChain_swap_matrix (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) :
    (targetChain a b ha hb n).matrix=
      -(alternatingMatrix (n+1)*(targetChain b a hb ha n).matrix*alternatingMatrix (n+1)) := by
  rw [targetChain_swap b a hb ha n]
  exact reflect_matrix _

end
end jacobi.Comparison

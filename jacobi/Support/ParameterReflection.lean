import jacobi.Support.CorrectedChain
import jacobi.Finite.Reflection

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The actual parameter-swapped natural support matrix is identified with
the genuine positive-coupling spectral reflection. The proof reuses
the complete actual cosine spectrum and finite persymmetric uniqueness,
including all admissible and exceptional source parameters.
Use: naturalChain_reflect_inFiber fixes the genuine reflected finite fibre, and support weight reflection uses this exact original node pairing.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix Polynomial jacobi.Reference jacobi.Finite chebyshev1 chebyshev2

/-- The actual support cosine lattice reflects exactly under swapping the original endpoint parameters and reversing the original node order.
Use: naturalChain_reflect_inFiber fixes the genuine reflected finite fibre, and support weight reflection uses this exact original node pairing.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: the already proved original affine phase reflection and cos(pi-x)=-cos(x) give the exact actual node identity. -/
theorem naturalNode_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (k:Fin n) :
    naturalNode a b n k.rev= -naturalNode b a n k := by
  rw [naturalNode,naturalNode,show k.rev.val=n-1-k.val by simp only [Fin.val_rev]; omega,
    jacobi.Jacobi.modelAngle_reflection ha hb k.isLt,Real.cos_pi_sub]

/-- The genuine positive-coupling reflection of the original support chain has exactly the original swapped cosine-node characteristic polynomial.
Use: naturalChain_swap applies the existing full persymmetric uniqueness theorem with no assumed spectrum.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: evaluate the actual reflected characteristic polynomial, insert the already proved complete original cosine product, move the exact sign inside that finite product, and reverse its genuine original node order. -/
theorem naturalChain_reflect_charpoly (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (reflect (naturalChain a b ha hb n)).matrix.charpoly=(naturalNodes b a hb ha n).polynomial := by
  -- Whole-polynomial equality fixes every genuine reflected spectral node, including its original multiplicity.
  apply Polynomial.funext
  intro x
  rw [reflect_charpoly_eval,naturalChain_charpoly]
  simp only [Nodes.polynomial,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  change (-1:ℝ)^n*(∏i:Fin n,(-x-naturalNode a b n i))=∏i:Fin n,(x-naturalNode b a n i)
  rw [show (-1:ℝ)^n=∏_i:Fin n,(-1:ℝ) by simp]
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i:Fin n,(-1:ℝ)*(-x-naturalNode a b n i))=
        ∏ i:Fin n,(x+naturalNode a b n i) := Finset.prod_congr rfl (fun _ _ => by ring)
    _ = ∏ i:Fin n,(x+naturalNode a b n i.rev) := (Equiv.prod_comp Fin.revPerm _).symm
    _ = _ := by simp only [naturalNode_reflection ha hb,sub_eq_add_neg]

/-- Swapping the actual original endpoint parameters negates precisely the diagonal and retains the actual positive support couplings.
Use: natural/support polynomial parity and the original reversed spectral weights connect the left support edge to the same proved right-edge theory.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the genuine reflected chain has the actual swapped full characteristic polynomial, is irreducible and is physically persymmetric. The earlier complete uniqueness theorem in that very finite fibre therefore identifies it with the original swapped support chain. -/
theorem naturalChain_swap (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    naturalChain b a hb ha (n+1)=reflect (naturalChain a b ha hb (n+1)) := by
  -- Both competing chains belong to the original swapped fibre with every premise already proved.
  let S := naturalNodes b a hb ha (n+1)
  let J : Fiber (n+1) S.polynomial :=
    ⟨reflect (naturalChain a b ha hb (n+1)),
      affine_irreducible (naturalChain_irreducible a b ha hb (n+1)) (by norm_num) 0,
      naturalChain_reflect_charpoly a b ha hb (n+1)⟩
  let K : Fiber (n+1) S.polynomial :=
    ⟨naturalChain b a hb ha (n+1),naturalChain_inFiber b a hb ha (n+1)⟩
  have h : K=J := (exists_unique_persymmetric S).unique
    (naturalChain_persymmetric b a hb ha (n+1))
    (reflect_persymmetric (naturalChain_reverse a b ha hb (n+1)))
  exact congrArg Subtype.val h

end
end jacobi.Support

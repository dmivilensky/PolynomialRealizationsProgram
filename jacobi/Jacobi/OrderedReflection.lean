import jacobi.Jacobi.Reflection
import jacobi.Jacobi.Nodes
import Mathlib.Order.Hom.Set

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The complete genuine shifted zero lists reflect in reverse order when the
Jacobi parameters are exchanged. This identifies the source's two edges
without an assumed correspondence of enumerations.
Use: supplies the numbered zero correspondence needed to extend every one-edge estimate to the opposite edge.
-/
namespace jacobi.Jacobi
noncomputable section
open Set

/-- The full genuine ordered shifted Jacobi zero list reflects exactly in reverse order under parameter exchange.
Use: supplies the numbered zero correspondence needed to extend every one-edge estimate to the opposite edge.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: reflection gives equality of the complete zero sets. Reversing the
finite order makes the reflected list strictly increasing. Two increasing
lists on Fin n with the same range agree, by the community order-embedding uniqueness theorem. -/
theorem shiftedRoots_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (i : Fin n) :
    shiftedRoots a b ha hb n i=1-shiftedRoots b a hb ha n i.rev := by
  -- Completeness and strict ordering were proved for the actual roots, before comparing the two enumerations.
  let g : Fin n → ℝ := fun j => 1-shiftedRoots b a hb ha n j.rev
  have hg : StrictMono g := by
    intro j k hjk
    have hh := (shiftedRoots b a hb ha n).strictMono (Fin.rev_lt_rev.mpr hjk)
    dsimp [g]
    linarith
  have hr : Set.range (shiftedRoots a b ha hb n)=Set.range g := by
    ext t
    constructor
    · rintro ⟨j,rfl⟩
      have hz := (shiftedRoots_exhaustive ha hb n _).mpr ⟨j,rfl⟩
      have hrz := (reflected_zero_iff hb ha n).mpr hz
      obtain ⟨k,hk⟩ := (shiftedRoots_exhaustive hb ha n _).mp hrz
      refine ⟨k.rev,?_⟩
      dsimp [g]
      rw [Fin.rev_rev,hk]
      ring
    · rintro ⟨j,rfl⟩
      have hz := (shiftedRoots_exhaustive hb ha n _).mpr ⟨j.rev,rfl⟩
      have hrz := (reflected_zero_iff ha hb n).mpr hz
      exact (shiftedRoots_exhaustive ha hb n _).mp hrz
  exact congrFun ((shiftedRoots a b ha hb n).strictMono.eq_of_range_eq hg hr) i

/-- The actual source Jacobi nodes have exactly the printed ordered parameter-reflection identity.
Use: transfers both-edge estimates and the opposite edge exponent using the source's canonical zero indices.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: replace the actual shifted root at the reversed index using the
proved complete ordered reflection; the affine coordinate x=1-2*t gives the negative node. -/
theorem nodes_reflection {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (i : Fin n) :
    (nodes a b ha hb n).value i.rev= -(nodes b a hb ha n).value i := by
  change 1-2*shiftedRoots a b ha hb n i.rev= -(1-2*shiftedRoots b a hb ha n i)
  rw [shiftedRoots_reflection ha hb i.rev,Fin.rev_rev]
  ring

end
end jacobi.Jacobi

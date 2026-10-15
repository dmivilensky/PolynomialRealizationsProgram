import «2610.05164v2».Packing.Representation
import «2610.05164v2».Green.Segments

/-!
Article: 2610.05164v2, Theorem 2.3.
Every contractive Jacobi chain has the article's interval packing, including all reducible chains.
Use: `«2610.05164v2».Packing.exists_representation` feeds
`«2610.05164v2».Packing.packedEigenvalue_summable` (packed Eigenvalue summable).
-/
namespace «2610.05164v2».Packing
noncomputable section
open Real Matrix Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/--
Every contractive Jacobi chain has the article's interval packing, including all reducible
chains. The induction splits an actual zero edge and translates one complete packing away from
the other.

The precise assertion is `Nonempty (Representation J.green gap)`.

Use: `«2610.05164v2».Packing.packing` uses this assertion in the displayed construction of
`packing`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3.

Proof: Induct on `N`; the recursive step uses the previous-stage assertion. Separate `0 < N`
from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem exists_representation (N : ℕ) (J : «2610.05164v2».Jacobi N)
    (hc : «2606.16671v2».opNorm J.matrix < 1) (gap : ℝ) (hg : 0 ≤ gap) : Nonempty (Representation J.green gap) := by
  -- Induct on `N`; the recursive step uses the previous-stage assertion.
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hN : 0 < N
    · by_cases hir : J.Irreducible
      · exact ⟨irreducibleRepresentation J hN hc hir gap⟩
      · obtain ⟨k,hk0,hkN,hkp⟩ : ∃ k, ∃ _ : 0 < k, ∃ _ : k < N, ¬0 < J.data.aSq k := by
          simpa only [«2610.05164v2».Jacobi.Irreducible,not_forall,not_imp] using hir
        have hz : J.data.aSq k = 0 := le_antisymm (le_of_not_gt hkp) (J.coupling_nonneg k)
        obtain ⟨P⟩ := ih k hkN (J.segment 0 k) (J.segment_contractive hc 0 k (by omega))
        obtain ⟨Q⟩ := ih (N-k) (by omega) (J.segment k (N-k)) (J.segment_contractive hc k (N-k) (by omega))
        let e := «2606.16671v2».JacobiData.splitIndex N ⟨k,by omega⟩
        have he : J.green.submatrix e e = Matrix.fromBlocks (J.segment 0 k).green 0 0 (J.segment k (N-k)).green :=
          J.zero_edge_green hc k (by omega) hz
        have R := (P.combine Q hg).reindex e.symm
        have hh : (Matrix.fromBlocks (J.segment 0 k).green 0 0 (J.segment k (N-k)).green).submatrix e.symm e.symm = J.green := by
          rw [← he,Matrix.submatrix_submatrix]
          ext i j
          simp only [Matrix.submatrix_apply,Function.comp_apply,Equiv.apply_symm_apply]
        exact ⟨hh ▸ R⟩
    · have hn : N = 0 := by omega
      subst N
      exact ⟨{
        point := Fin.elim0
        left := Fin.elim0
        right := Fin.elim0
        diagonal_pos := fun i => Fin.elim0 i
        length := fun i => Fin.elim0 i
        point_mem := fun i => Fin.elim0 i
        disjoint := fun i => Fin.elim0 i
        error := fun i => Fin.elim0 i }⟩

end
end «2610.05164v2».Packing

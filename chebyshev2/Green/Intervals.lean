import chebyshev2.Green.PackingGeometry
import Mathlib.Topology.Order.Real

/-!
Article: chebyshev2, Theorem 2.3.
Proposition 1: the constructed closed intervals have pairwise disjoint interiors.
Use: `chebyshev2.Jacobi.intervals_ordered` feeds
`chebyshev2.Jacobi.packingInterval_disjoint_interiors` (Proposition 1: the constructed closed
intervals have pairwise disjoint interiors).
Proof chain: `chebyshev2.Packing.exists_representation` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Jacobi
noncomputable section
open Real Matrix
open scoped Matrix Topology
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Defines `intervalLeft` of type `ℝ` by `if i.val = 0 then J.representationPoint hN i-1/J.green i
i else if i.val+1 = N then J.representationPoint hN i else max (J.lift.position (by omega)
⟨2*i.val-1,by omega⟩) (J.representationPoint hN i-1/J.green i i)`.

Use: `chebyshev2.Jacobi.even_le_intervalLeft` rewrites with this definition to establish
the stated quantitative bound `J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ ≤ J.intervalLeft
hN i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def intervalLeft (hN : 0 < N) (i : Fin N) : ℝ :=
  if i.val = 0 then J.representationPoint hN i-1/J.green i i
  else if i.val+1 = N then J.representationPoint hN i
  else max (J.lift.position (by omega) ⟨2*i.val-1,by omega⟩)
    (J.representationPoint hN i-1/J.green i i)

/--
Defines `intervalRight` of type `ℝ` by `J.intervalLeft hN i+1/J.green i i`.

Use: `chebyshev2.Jacobi.intervalRight_le_even` rewrites with this definition to establish
the stated quantitative bound `J.intervalRight hN i ≤ J.lift.position (by omega) ⟨2*i.val+1,by
omega⟩`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def intervalRight (hN : 0 < N) (i : Fin N) : ℝ := J.intervalLeft hN i+1/J.green i i
/--
Defines `packingInterval` of type `(hN : 0 < N) (i : Fin N)` by `Set.Icc (J.intervalLeft hN i)
(J.intervalRight hN i)`.

Use: `chebyshev2.Jacobi.packingInterval_disjoint_interiors` rewrites with this definition
to establish `Disjoint (interior (J.packingInterval hN i)) (interior
(J.packingInterval hN j))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def packingInterval (hN : 0 < N) (i : Fin N) := Set.Icc (J.intervalLeft hN i) (J.intervalRight hN i)

/--
Exact identity `J.intervalRight hN i-J.intervalLeft hN i = 1/J.green i i`.

Use: `chebyshev2.Packing.Jacobi.blocks_weight` rewrites with this identity to establish
exact identity `(blocks J hN ht hir).height i^2 * ((blocks J hN ht hir).right i-(blocks J hN ht
hir).left i) = atomicWeight J i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem interval_length (hN : 0 < N) (i : Fin N) :
    J.intervalRight hN i-J.intervalLeft hN i = 1/J.green i i := by dsimp [intervalRight]; ring

/--
Membership in the specified domain/enclosure: `J.representationPoint hN i ∈ J.packingInterval
hN i`.

Use: `chebyshev2.Packing.Jacobi.coupling_cost_bound` uses this assertion to establish the
stated quantitative bound `(∫ z, |z.1-z.2| ∂(blocks J hN ht hir).coupling
(J.representationPoint hN)) ≤ 1/(2*(N : ℝ))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Separate `i.val = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem representationPoint_mem_interval (hN : 0 < N) (h : chebyshev1.opNorm J.matrix < 1)
    (hir : J.Irreducible) (i : Fin N) : J.representationPoint hN i ∈ J.packingInterval hN i := by
  -- Separate `i.val = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  have hl : 0 < 1/J.green i i := one_div_pos.mpr hm.inv.diag_pos
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  have hx := (J.lift.position_strictMono (by omega) hm' hc.2 hc.1).monotone
  change J.intervalLeft hN i ≤ J.representationPoint hN i ∧
    J.representationPoint hN i ≤ J.intervalLeft hN i+1/J.green i i
  by_cases hi : i.val = 0
  · simp only [intervalLeft, hi, ite_true]; constructor <;> linarith
  · by_cases hin : i.val+1 = N
    · simp only [intervalLeft, hi, ite_false, hin, ite_true]; constructor <;> linarith
    · have he : J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ ≤ J.representationPoint hN i := by
        apply hx
        change (⟨2*i.val-1,by omega⟩ : Fin (2*N)).val ≤
          (Centering.interleave N (Sum.inl i)).val
        simp only [Centering.interleave_left]; omega
      simp only [intervalLeft, hi, hin, ite_false]
      constructor
      · exact max_le he (by linarith)
      · have hh := le_max_right (J.lift.position (by omega) ⟨2*i.val-1,by omega⟩)
          (J.representationPoint hN i-1/J.green i i)
        linarith

/--
The stated quantitative bound `J.intervalRight hN i ≤ J.lift.position (by omega) ⟨2*i.val+1,by
omega⟩`.

Use: `chebyshev2.Jacobi.intervals_ordered` uses this bound to establish the stated
quantitative bound `J.intervalRight hN i ≤ J.intervalLeft hN j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Separate `i.val = 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem intervalRight_le_even (hN : 0 < N) (h : chebyshev1.opNorm J.matrix < 1)
    (hir : J.Irreducible) (i : Fin N) (hin : i.val+1 < N) :
    J.intervalRight hN i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ := by
  -- Separate `i.val = 0` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  have hx := (J.lift.position_strictMono (by omega) hm' hc.2 hc.1).monotone
  have hy : J.representationPoint hN i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ := by
    apply hx
    change (Centering.interleave N (Sum.inl i)).val ≤ 2*i.val+1
    simp
  by_cases hi : i.val = 0
  · simpa [intervalRight, intervalLeft, hi] using hy
  · have hi0 : 0 < i.val := by omega
    have hn : ¬i.val+1 = N := by omega
    have hr := J.lift_interval_room hN h hir i hi0 hin
    simp only [intervalRight, intervalLeft, hi, hn, ite_false]
    rw [← max_add_add_right, max_le_iff]
    constructor <;> linarith

/--
The stated quantitative bound `J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ ≤ J.intervalLeft
hN i`.

Use: `chebyshev2.Jacobi.intervals_ordered` uses this bound to establish the stated
quantitative bound `J.intervalRight hN i ≤ J.intervalLeft hN j`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.pencils_of_contractive`,
`chebyshev2.Jacobi.lift_pencils`, `chebyshev2.Jacobi.lift_centered` with the arguments
shown in the proof.
-/
theorem even_le_intervalLeft (hN : 0 < N) (h : chebyshev1.opNorm J.matrix < 1)
    (hir : J.Irreducible) (i : Fin N) (hi : 0 < i.val) :
    J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ ≤ J.intervalLeft hN i := by
  -- Use the identities/estimates `chebyshev2.Jacobi.pencils_of_contractive`,
  -- `chebyshev2.Jacobi.lift_pencils`, `chebyshev2.Jacobi.lift_centered` with the
  -- arguments shown in the proof.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  have hx := (J.lift.position_strictMono (by omega) hm' hc.2 hc.1).monotone
  simp only [intervalLeft, show i.val ≠ 0 by omega, ite_false]
  split_ifs
  · apply hx
    change 2*i.val-1 ≤ (Centering.interleave N (Sum.inl i)).val
    simp
  · exact le_max_left _ _

/--
The stated quantitative bound `J.intervalRight hN i ≤ J.intervalLeft hN j`.

Use: `chebyshev2.Jacobi.packingInterval_disjoint_interiors` uses this bound to establish
the precise assertion is `Disjoint (interior (J.packingInterval hN i)) (interior
(J.packingInterval hN j))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.pencils_of_contractive`,
`chebyshev2.Jacobi.lift_pencils`, `chebyshev2.Jacobi.lift_centered` with the arguments
shown in the proof.
-/
theorem intervals_ordered (hN : 0 < N) (h : chebyshev1.opNorm J.matrix < 1)
    (hir : J.Irreducible) (i j : Fin N) (hij : i.val < j.val) :
    J.intervalRight hN i ≤ J.intervalLeft hN j := by
  -- Use the identities/estimates `chebyshev2.Jacobi.pencils_of_contractive`,
  -- `chebyshev2.Jacobi.lift_pencils`, `chebyshev2.Jacobi.lift_centered` with the
  -- arguments shown in the proof.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  have hx := (J.lift.position_strictMono (by omega) hm' hc.2 hc.1).monotone
  apply (J.intervalRight_le_even hN h hir i (by omega)).trans
  apply le_trans ?_ (J.even_le_intervalLeft hN h hir j (by omega))
  apply hx
  change 2*i.val+1 ≤ 2*j.val-1
  omega

/--
Proposition 1: the constructed closed intervals have pairwise disjoint interiors.

The precise assertion is `Disjoint (interior (J.packingInterval hN i)) (interior
(J.packingInterval hN j))`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 2.3.

Proof: Use the identities/estimates `chebyshev2.Jacobi.intervals_ordered` with the
arguments shown in the proof.
-/
theorem packingInterval_disjoint_interiors (hN : 0 < N) (h : chebyshev1.opNorm J.matrix < 1)
    (hir : J.Irreducible) (i j : Fin N) (hij : i ≠ j) :
    Disjoint (interior (J.packingInterval hN i)) (interior (J.packingInterval hN j)) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.intervals_ordered` with the arguments
  -- shown in the proof.
  rw [packingInterval, packingInterval, interior_Icc, interior_Icc]
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hv : i.val ≠ j.val := fun he => hij (Fin.ext he)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have he := J.intervals_ordered hN h hir i j hlt
    exact (not_lt_of_ge he) (hj.1.trans hi.2)
  · have he := J.intervals_ordered hN h hir j i hgt
    exact (not_lt_of_ge he) (hi.1.trans hj.2)

end
end chebyshev2.Jacobi

import «2610.05164v2».Green.Intervals
import «2610.05164v2».Packing.Blocks

/-!
Article: 2610.05164v2, Theorem 2.3.
Proposition 1 supplies the exact one-block packing at every requested gap.
Use: `«2610.05164v2».Packing.irreducibleRepresentation` feeds
`«2610.05164v2».Packing.exists_representation` (Every contractive Jacobi chain has the article's
interval packing, including all reducible chains).
Proof chain: `«2610.05164v2».Packing.exists_representation` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Packing
noncomputable section
open Real Set Matrix
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/--
Interval packing with a controlled exponential Gram matrix error. All fields describe actual
points, intervals and entries of the input matrix.

Use: `«2610.05164v2».Packing.Representation.combine` uses this record of data and proof
obligations in the displayed construction of `combine`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
structure Representation {ι : Type*} (G : Matrix ι ι ℝ) (gap : ℝ) where
  /-- Point assigned to each Green-matrix index. -/
  point : ι → ℝ
  /-- Left endpoint of its spreading interval. -/
  left : ι → ℝ
  /-- Right endpoint of its spreading interval. -/
  right : ι → ℝ
  /-- Every Green diagonal entry is positive, so its inverse defines an interval length. -/
  diagonal_pos : ∀ i, 0 < G i i
  /-- The interval length is the inverse Green diagonal, preserving the prescribed cell mass/energy scaling. -/
  length : ∀ i, right i-left i = 1/G i i
  /-- The point representative lies inside its own spreading interval. -/
  point_mem : ∀ i, point i ∈ Icc (left i) (right i)
  /-- Spreading intervals have disjoint interiors in the half-open convention, allowing additive density integrals. -/
  disjoint : Pairwise fun i j => Disjoint (Ioc (left i) (right i)) (Ioc (left j) (right j))
  /-- Explicit exponential-kernel approximation error in terms of the separation gap and Green diagonals. -/
  error : ∀ i j, |G i j-sqrt (G i i*G j j)*exp (-|point i-point j|)| ≤ exp (-gap)*sqrt (G i i*G j j)

namespace Representation
variable {ι κ : Type*} {G : Matrix ι ι ℝ} {H : Matrix κ κ ℝ} {gap : ℝ}

/--
The precise assertion is `Disjoint (interior (Icc (P.left i) (P.right i))) (interior (Icc
(P.left j) (P.right j)))`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem disjoint_interiors (P : Representation G gap) {i j : ι} (hij : i ≠ j) :
    Disjoint (interior (Icc (P.left i) (P.right i))) (interior (Icc (P.left j) (P.right j))) := by
  rw [interior_Icc,interior_Icc]
  exact (P.disjoint hij).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

/--
Relabeling preserves the actual packing and all its bounds.

Use: `«2610.05164v2».Packing.exists_representation` uses this definition to establish the
precise assertion is `Nonempty (Representation J.green gap)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def reindex (P : Representation G gap) (e : κ ≃ ι) : Representation (G.submatrix e e) gap where
  point i := P.point (e i)
  left i := P.left (e i)
  right i := P.right (e i)
  diagonal_pos i := P.diagonal_pos (e i)
  length i := P.length (e i)
  point_mem i := P.point_mem (e i)
  disjoint _i _j hij := P.disjoint (fun h => hij (e.injective h))
  error i j := P.error (e i) (e j)

variable [Fintype ι] [Fintype κ]

/--
A finite explicit translation separates every interval in the two families.

Use: `«2610.05164v2».Packing.Representation.combine` uses this definition in the displayed
construction of `combine`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def separationShift (P : Representation G gap) (Q : Representation H gap) : ℝ :=
  (∑ i, |P.right i|)+(∑ j, |Q.left j|)+gap

/--
The stated quantitative bound `P.right i+gap ≤ Q.left j+P.separationShift Q`.

Use: `«2610.05164v2».Packing.Representation.combine` uses this bound in the displayed
construction of `combine`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem separationShift_le (P : Representation G gap) (Q : Representation H gap) (i : ι) (j : κ) :
    P.right i+gap ≤ Q.left j+P.separationShift Q := by
  have hi : |P.right i| ≤ ∑ i, |P.right i| := Finset.single_le_sum (f := fun i => |P.right i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hj : |Q.left j| ≤ ∑ j, |Q.left j| := Finset.single_le_sum (f := fun j => |Q.left j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  dsimp [separationShift]
  linarith [le_abs_self (P.right i),neg_le_abs (Q.left j)]

/--
Place two block diagonal realizations on a common real line.

Use: `«2610.05164v2».Packing.exists_representation` uses this definition to establish the
precise assertion is `Nonempty (Representation J.green gap)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def combine (P : Representation G gap) (Q : Representation H gap) (hg : 0 ≤ gap) :
    Representation (Matrix.fromBlocks G 0 0 H) gap where
  point := Sum.elim P.point (fun j => Q.point j+P.separationShift Q)
  left := Sum.elim P.left (fun j => Q.left j+P.separationShift Q)
  right := Sum.elim P.right (fun j => Q.right j+P.separationShift Q)
  diagonal_pos i := by cases i with
    | inl i => exact P.diagonal_pos i
    | inr i => exact Q.diagonal_pos i
  length i := by cases i with
    | inl i => exact P.length i
    | inr i =>
      change Q.right i+P.separationShift Q-(Q.left i+P.separationShift Q) = 1/H i i
      rw [show Q.right i+P.separationShift Q-(Q.left i+P.separationShift Q)=Q.right i-Q.left i by ring]
      exact Q.length i
  point_mem i := by cases i with
    | inl i => exact P.point_mem i
    | inr i =>
      change Q.left i+P.separationShift Q ≤ Q.point i+P.separationShift Q ∧
        Q.point i+P.separationShift Q ≤ Q.right i+P.separationShift Q
      constructor <;> linarith [(Q.point_mem i).1,(Q.point_mem i).2]
  disjoint i j hij := by
    cases i with
    | inl i => cases j with
      | inl j => exact P.disjoint (fun h => hij (congrArg Sum.inl h))
      | inr j =>
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hs := P.separationShift_le Q i j
        have hx := hx.2
        change x ≤ P.right i at hx
        have hy := hy.1
        change Q.left j+P.separationShift Q < x at hy
        linarith
    | inr i => cases j with
      | inl j =>
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hs := P.separationShift_le Q j i
        have hx := hx.1
        change Q.left i+P.separationShift Q < x at hx
        have hy := hy.2
        change x ≤ P.right j at hy
        linarith
      | inr j =>
        apply Set.disjoint_left.mpr
        intro x hx hy
        change Q.left i+P.separationShift Q < x ∧ x ≤ Q.right i+P.separationShift Q at hx
        change Q.left j+P.separationShift Q < x ∧ x ≤ Q.right j+P.separationShift Q at hy
        have hd := Set.disjoint_left.mp (Q.disjoint (fun h => hij (congrArg Sum.inr h)))
        apply hd (a := x-P.separationShift Q)
        · constructor <;> linarith [hx.1,hx.2]
        · constructor <;> linarith [hy.1,hy.2]
  error i j := by
    cases i with
    | inl i => cases j with
      | inl j => exact P.error i j
      | inr j =>
        change |0-sqrt (G i i*H j j)*exp (-|P.point i-(Q.point j+P.separationShift Q)|)| ≤ _
        have hs := P.separationShift_le Q i j
        have hd : gap ≤ |P.point i-(Q.point j+P.separationShift Q)| := by
          have h := neg_le_abs (P.point i-(Q.point j+P.separationShift Q))
          linarith [(P.point_mem i).2,(Q.point_mem j).1]
        rw [zero_sub,abs_neg,abs_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hd)) (sqrt_nonneg _)).trans_eq (mul_comm _ _)
    | inr i => cases j with
      | inl j =>
        change |0-sqrt (H i i*G j j)*exp (-|Q.point i+P.separationShift Q-P.point j|)| ≤ _
        have hs := P.separationShift_le Q j i
        have hd : gap ≤ |Q.point i+P.separationShift Q-P.point j| := by
          have h := le_abs_self (Q.point i+P.separationShift Q-P.point j)
          linarith [(P.point_mem j).2,(Q.point_mem i).1]
        rw [zero_sub,abs_neg,abs_of_nonneg (by positivity)]
        exact (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hd)) (sqrt_nonneg _)).trans_eq (mul_comm _ _)
      | inr j =>
        change |H i j-sqrt (H i i*H j j)*exp (-|(Q.point i+_)-(Q.point j+_)|)| ≤ _
        rw [show Q.point i+P.separationShift Q-(Q.point j+P.separationShift Q) = Q.point i-Q.point j by ring]
        exact Q.error i j

end Representation

/--
Proposition 1 supplies the exact one-block packing at every requested gap.

Use: `«2610.05164v2».Packing.exists_representation` uses this definition to establish the
precise assertion is `Nonempty (Representation J.green gap)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def irreducibleRepresentation {N : ℕ} (J : «2610.05164v2».Jacobi N) (hN : 0 < N)
    (hc : «2606.16671v2».opNorm J.matrix < 1) (hir : J.Irreducible) (gap : ℝ) : Representation J.green gap where
  point := J.representationPoint hN
  left := J.intervalLeft hN
  right := J.intervalRight hN
  diagonal_pos i := (J.pencils_of_contractive hc).1.inv.diag_pos
  length := J.interval_length hN
  point_mem := J.representationPoint_mem_interval hN hc hir
  disjoint i j hij := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · have he := J.intervals_ordered hN hc hir i j h
      linarith [hx.2,hy.1]
    · have he := J.intervals_ordered hN hc hir j i h
      linarith [hx.1,hy.2]
  error i j := by rw [J.green_representation hN hc hir i j,sub_self,abs_zero]; positivity

end
end «2610.05164v2».Packing

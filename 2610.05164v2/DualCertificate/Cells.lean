import «2610.05164v2».Residual.Price
import Mathlib.Topology.Order.MonotoneContinuity

/-!
Article: 2610.05164v2, Theorem 3.6.
The closed rational cells and affine prices of Definition 7(iv).
Use: `«2610.05164v2».DualCertificate.Cells.value_continuousAt` feeds
`«2610.05164v2».DualCertificate.Data.cellPrice_continuousAt` (cell Price continuous At).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set Filter Real «2610.05164v2».Residual
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
An ordered rational partition of [0,1] with an affine price on each cell. Its proof fields give
nonempty cells, interior disjointness and full closed-interval coverage.

Use: `«2610.05164v2».DualCertificate.Cells.affine` uses this record of data and proof
obligations in the displayed construction of `affine`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
structure Cells where
  /-- Number of intervals in this side of the certificate partition. -/
  count : ℕ
  /-- Rational lower endpoint of each cell. -/
  lo : Fin count → ℚ
  /-- Rational upper endpoint of each cell. -/
  hi : Fin count → ℚ
  /-- Constant coefficient of the cellwise affine price. -/
  intercept : Fin count → ℚ
  /-- Linear coefficient of the cellwise affine price. -/
  slope : Fin count → ℚ
  /-- Every cell has positive width. -/
  nonempty : ∀ i, lo i<hi i
  /-- Every cell lies in the normalized coordinate interval [0,1]. -/
  inside : ∀ i, 0≤lo i ∧ hi i≤1
  /-- Cells occur in order and have disjoint interiors; touching endpoints are permitted. -/
  ordered : ∀ i j, i<j → hi i≤lo j
  /-- Every point of [0,1] belongs to at least one closed cell, so cellwise inequalities cover the complete side. -/
  cover : ∀ t ∈ Icc (0:ℝ) 1, ∃ i, t ∈ Icc (lo i:ℝ) (hi i:ℝ)

namespace Cells
variable (P : Cells)

/--
Defines `affine` of type `ℝ` by `(P.intercept i:ℝ)+(P.slope i:ℝ)*t`.

Use: `«2610.05164v2».DualCertificate.Cells.value` uses this definition in the displayed
construction of `value`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def affine (i : Fin P.count) (t : ℝ) : ℝ := (P.intercept i:ℝ)+(P.slope i:ℝ)*t
/--
Defines `index` of type `Fin P.count` by `Classical.choose (P.cover t ht)`.

Use: `«2610.05164v2».DualCertificate.Cells.value` uses this definition in the displayed
construction of `value`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def index (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : Fin P.count := Classical.choose (P.cover t ht)
/--
Defines `value` of type `ℝ` by `if ht : t ∈ Icc (0:ℝ) 1 then P.affine (P.index t ht) t else 0`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this definition in the displayed
construction of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def value (t : ℝ) : ℝ := if ht : t ∈ Icc (0:ℝ) 1 then P.affine (P.index t ht) t else 0
/--
Defines `endpoints` of type `Finset ℝ` by `Finset.univ.image (fun i => (P.lo i:ℝ)) ∪
Finset.univ.image (fun i => (P.hi i:ℝ))`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this definition in the displayed
construction of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def endpoints : Finset ℝ :=
  Finset.univ.image (fun i => (P.lo i:ℝ)) ∪ Finset.univ.image (fun i => (P.hi i:ℝ))
/--
Defines `bound` of type `ℝ` by `∑ i, (|((P.intercept i):ℝ)|+|((P.slope i):ℝ)|)`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this definition in the displayed
construction of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def bound : ℝ := ∑ i, (|((P.intercept i):ℝ)|+|((P.slope i):ℝ)|)

/--
Membership in the specified domain/enclosure: `t ∈ Icc (P.lo (P.index t ht):ℝ) (P.hi (P.index t
ht):ℝ)`.

Use: `«2610.05164v2».DualCertificate.Cells.value_continuousAt` uses this assertion to establish
continuity at the stated point: `ContinuousAt P.value t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem index_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    t ∈ Icc (P.lo (P.index t ht):ℝ) (P.hi (P.index t ht):ℝ) :=
  Classical.choose_spec (P.cover t ht)

/--
The precise assertion is `Icc (P.lo i:ℝ) (P.hi i:ℝ) ⊆ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».DualCertificate.Cells.value_on_interior` uses this assertion to establish
exact identity `P.value t=P.affine i t`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem cell_inside (i : Fin P.count) : Icc (P.lo i:ℝ) (P.hi i:ℝ) ⊆ Icc (0:ℝ) 1 := by
  intro t ht
  have h := P.inside i
  have h₀ : (0:ℝ)≤P.lo i := by exact_mod_cast h.1
  have h₁ : (P.hi i:ℝ)≤1 := by exact_mod_cast h.2
  exact ⟨h₀.trans ht.1,ht.2.trans h₁⟩

/--
Exact identity `j=i`.

Use: `«2610.05164v2».DualCertificate.Cells.value_on_interior` rewrites with this identity to
establish exact identity `P.value t=P.affine i t`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem interior_unique {i j : Fin P.count} {t : ℝ}
    (hi : t ∈ Ioo (P.lo i:ℝ) (P.hi i:ℝ))
    (hj : t ∈ Icc (P.lo j:ℝ) (P.hi j:ℝ)) : j=i := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  rcases lt_trichotomy j i with h | h | h
  · have ho : (P.hi j:ℝ)≤P.lo i := by exact_mod_cast P.ordered j i h
    linarith [hi.1,hj.2]
  · exact h
  · have ho : (P.hi i:ℝ)≤P.lo j := by exact_mod_cast P.ordered i j h
    linarith [hi.2,hj.1]

/--
Exact identity `P.value t=P.affine i t`.

Use: `«2610.05164v2».DualCertificate.Cells.value_continuousAt` uses this identity to establish
continuity at the stated point: `ContinuousAt P.value t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.Cells.cell_inside`,
`«2610.05164v2».DualCertificate.Cells.interior_unique`,
`«2610.05164v2».DualCertificate.Cells.index_mem` with the arguments shown in the proof.
-/
theorem value_on_interior {i : Fin P.count} {t : ℝ}
    (ht : t ∈ Ioo (P.lo i:ℝ) (P.hi i:ℝ)) : P.value t=P.affine i t := by
  have hin := P.cell_inside i ⟨ht.1.le,ht.2.le⟩
  rw [value,dite_eq_left hin]
  rw [P.interior_unique ht (P.index_mem hin)]

/--
The stated quantitative bound `0≤P.bound`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this bound in the displayed construction
of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem bound_nonneg : 0≤P.bound :=
  Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))

/--
The stated quantitative bound `‖P.value t‖≤P.bound`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this bound in the displayed construction
of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t ∈ Icc (0:ℝ) 1` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem value_bound (t : ℝ) : ‖P.value t‖≤P.bound := by
  -- Separate `t ∈ Icc (0:ℝ) 1` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · rw [value,dite_eq_left ht]
    let i := P.index t ht
    have hi : |(P.intercept i:ℝ)|+|(P.slope i:ℝ)|≤P.bound := by
      unfold bound
      exact Finset.single_le_sum (f := fun j : Fin P.count =>
        |(P.intercept j:ℝ)|+|(P.slope j:ℝ)|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    apply le_trans _ hi
    dsimp only [affine]
    rw [norm_eq_abs]
    calc
      _ ≤ |(P.intercept i:ℝ)|+|(P.slope i:ℝ)*t| := abs_add_le _ _
      _ ≤ |(P.intercept i:ℝ)|+|(P.slope i:ℝ)| := by
        rw [abs_mul,abs_of_nonneg ht.1]
        exact add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) ht.2)
  · rw [value,dite_eq_right ht,norm_zero]
    exact P.bound_nonneg

/--
Continuity at the stated point: `ContinuousAt P.value t`.

Use: `«2610.05164v2».DualCertificate.Cells.price` uses this continuity result in the displayed
construction of `price`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t ∈ Icc (0:ℝ) 1` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then
prove the asserted relation at an arbitrary point in that intersection.
-/
theorem value_continuousAt {t : ℝ} (ht : t ∉ P.endpoints) : ContinuousAt P.value t := by
  -- Separate `t ∈ Icc (0:ℝ) 1` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hin : t ∈ Icc (0:ℝ) 1
  · let i := P.index t hin
    have hi := P.index_mem hin
    have hlo : t≠(P.lo i:ℝ) := fun he => ht (by simp [endpoints,he])
    have hhi : t≠(P.hi i:ℝ) := fun he => ht (by simp [endpoints,he])
    have hti : t ∈ Ioo (P.lo i:ℝ) (P.hi i:ℝ) :=
      ⟨lt_of_le_of_ne hi.1 (Ne.symm hlo),lt_of_le_of_ne hi.2 hhi⟩
    apply (show ContinuousAt (P.affine i) t by unfold affine; fun_prop).congr
    filter_upwards [isOpen_Ioo.mem_nhds hti] with u hu
    exact (P.value_on_interior hu).symm
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) t).congr
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hin] with u hu
    rw [value,dite_eq_right hu]

/--
Constructs `price` of type `Price` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: a standalone supporting definition for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.6.
-/
def price : Price where
  value := P.value
  exceptional := P.endpoints
  continuous := fun _ ht => P.value_continuousAt ht
  B := P.bound
  bound_nonneg := P.bound_nonneg
  bound := P.value_bound

end Cells
end
end «2610.05164v2».DualCertificate

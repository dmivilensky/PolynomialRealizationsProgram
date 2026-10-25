import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Article: chebyshev1, Proposition 1.3.
Exact constant + linear + higher-order decomposition (algebraic Proposition 1.3).
Use: `chebyshev1.orderedProduct_add_decomposition` feeds
`chebyshev1.Realization.operatorTransfer_decomposition` (Proposition 1.3: an exact identity,
without any smallness assumption on the drift).
Proof chain: `chebyshev1.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product. The needed form is proved here.
-/
namespace chebyshev1

open scoped BigOperators

variable {A : Type*}

/--
`C (n-1) * ... * C 0`, with the empty product equal to one.

Use: `chebyshev1.insertionTerm` uses this definition in the displayed construction of
`insertionTerm`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def orderedProduct [Monoid A] (C : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => C n * orderedProduct C n

/--
Exact identity `orderedProduct C 0 = 1`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev1, Proposition 1.3.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem orderedProduct_zero [Monoid A] (C : ℕ → A) :
    orderedProduct C 0 = 1 := rfl

/--
Exact identity `orderedProduct C (n + 1) = C n * orderedProduct C n`.

Use: `chebyshev1.insertionTerm_insert_max` rewrites with this identity to establish exact
identity `insertionTerm C D n (insert s S) = orderedProduct (fun i => C (s + 1 + i)) (n - (s +
1)) * D s * insertionTerm C D s S`.

Article: chebyshev1, Theorem 2.1 via `chebyshev1.Prefix.quadraticError_exact`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem orderedProduct_succ [Monoid A] (C : ℕ → A) (n : ℕ) :
    orderedProduct C (n + 1) = C n * orderedProduct C n := rfl

/--
Exact identity `orderedProduct C n = orderedProduct D n`.

Use: `chebyshev1.insertionTerm_insert_last` uses this identity to establish the identity
`insertionTerm C D (n + 1) (insert n S) = D n * insertionTerm C D n S`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem orderedProduct_congr [Monoid A] {C D : ℕ → A} {n : ℕ}
    (h : ∀ i < n, C i = D i) : orderedProduct C n = orderedProduct D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [orderedProduct_succ]
    rw [h n (by omega), ih (fun i hi => h i (by omega))]

/--
Splitting a causal product at a time boundary.

Exact identity `orderedProduct C (a + b) = orderedProduct (fun i => C (a + i)) b *
orderedProduct C a`.

Use: `chebyshev1.insertionTerm_insert_max` rewrites with this identity to establish exact
identity `insertionTerm C D n (insert s S) = orderedProduct (fun i => C (s + 1 + i)) (n - (s +
1)) * D s * insertionTerm C D s S`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Induct on `b`; the recursive step uses the previous-stage assertion.
-/
theorem orderedProduct_add [Monoid A] (C : ℕ → A) (a b : ℕ) :
    orderedProduct C (a + b) =
      orderedProduct (fun i => C (a + i)) b * orderedProduct C a := by
  -- Induct on `b`; the recursive step uses the previous-stage assertion.
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, orderedProduct_succ,
      orderedProduct_succ, ih, mul_assoc]

/--
A change at one time has a fixed tail and prefix.

Exact identity `orderedProduct (Function.update C s v) n = orderedProduct (fun i => C (s + 1 +
i)) (n - (s + 1)) * v * orderedProduct C s`.

Use: `chebyshev1.insertionMultilinear` uses this identity in the displayed construction of
`insertionMultilinear`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_add`,
`chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the arguments
shown in the proof.
-/
theorem orderedProduct_update [Monoid A] (C : ℕ → A) (v : A) {n s : ℕ} (hs : s < n) :
    orderedProduct (Function.update C s v) n =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) * v * orderedProduct C s := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_add`,
  -- `chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the
  -- arguments shown in the proof.
  rw [show n = (s + 1) + (n - (s + 1)) by omega, orderedProduct_add,
    orderedProduct_succ, Function.update_self]
  have htail : orderedProduct (fun i => Function.update C s v (s + 1 + i))
      (n - (s + 1)) = orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) := by
    apply orderedProduct_congr
    intro i _
    simp [Function.update_of_ne (show s + 1 + i ≠ s by omega)]
  have hprefix : orderedProduct (Function.update C s v) s = orderedProduct C s := by
    apply orderedProduct_congr
    intro i hi
    simp [Function.update_of_ne (show i ≠ s by omega)]
  rw [htail, hprefix, mul_assoc]
  simp

/--
Replace the steps indexed by `S` by insertions `D`.

Use: `chebyshev1.degreeTerm` uses this definition in the displayed construction of
`degreeTerm`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def insertionTerm [Monoid A] (C D : ℕ → A) (n : ℕ) (S : Finset ℕ) : A :=
  orderedProduct (fun i => if i ∈ S then D i else C i) n

/--
Exact identity `insertionTerm C D n ∅ = orderedProduct C n`.

Use: `chebyshev1.degreeTerm_zero` uses this identity to establish the identity
`degreeTerm C D n 0 = orderedProduct C n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem insertionTerm_empty [Monoid A] (C D : ℕ → A) (n : ℕ) :
    insertionTerm C D n ∅ = orderedProduct C n := by simp [insertionTerm]

/--
Exact identity `insertionTerm C D (n + 1) (insert n S) = D n * insertionTerm C D n S`.

Use: `chebyshev1.orderedProduct_add_expansion` uses this identity to establish exact
identity `orderedProduct (fun i => C i + D i) n = ∑ S ∈ (Finset.range n).powerset,
insertionTerm C D n S`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_congr` with the arguments
shown in the proof.
-/
theorem insertionTerm_insert_last [Monoid A] (C D : ℕ → A) (n : ℕ)
    (S : Finset ℕ) :
    insertionTerm C D (n + 1) (insert n S) = D n * insertionTerm C D n S := by
  simp only [insertionTerm, orderedProduct_succ, Finset.mem_insert_self, ite_true]
  congr 1
  apply orderedProduct_congr
  intro i hi
  simp [show i ≠ n by omega]

/--
The exact finite expansion, indexed by insertion times; no commutativity is used.

Exact identity `orderedProduct (fun i => C i + D i) n = ∑ S ∈ (Finset.range n).powerset,
insertionTerm C D n S`.

Use: `chebyshev1.orderedProduct_add_by_degree` rewrites with this identity to establish
exact identity `orderedProduct (fun i => C i + D i) n = ∑ k ∈ Finset.range (n + 1), degreeTerm
C D n k`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Identify the
summands/integrands on their required domain before replacing the sum or integral.
-/
theorem orderedProduct_add_expansion [Semiring A] (C D : ℕ → A) (n : ℕ) :
    orderedProduct (fun i => C i + D i) n =
      ∑ S ∈ (Finset.range n).powerset, insertionTerm C D n S := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [insertionTerm]
  | succ n ih =>
    rw [orderedProduct_succ, add_mul, ih, Finset.range_add_one,
      Finset.sum_powerset_insert (by simp)]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro S hS
      have hn : n ∉ S := Finset.notMem_of_mem_powerset_of_notMem hS (by simp)
      simp [insertionTerm, hn]
    · apply Finset.sum_congr rfl
      intro S _
      exact (insertionTerm_insert_last C D n S).symm

/--
The contribution with exactly `k` insertions.

Use: `chebyshev1.degreeTerm_one` rewrites with this definition to establish the identity
`degreeTerm C D n 1 = ∑ s ∈ Finset.range n, insertionTerm C D n {s}`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def degreeTerm [Semiring A] (C D : ℕ → A) (n k : ℕ) : A :=
  ∑ S ∈ (Finset.range n).powersetCard k, insertionTerm C D n S

/--
The expansion stops at order `n`.

Exact identity `orderedProduct (fun i => C i + D i) n = ∑ k ∈ Finset.range (n + 1), degreeTerm
C D n k`.

Use: `chebyshev1.orderedProduct_add_decomposition` rewrites with this identity to establish
exact identity `orderedProduct (fun i => C i + D i) n = orderedProduct C n + firstVariation C D
n + higherOrder C D n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_add_expansion` with the
arguments shown in the proof.
-/
theorem orderedProduct_add_by_degree [Semiring A] (C D : ℕ → A) (n : ℕ) :
    orderedProduct (fun i => C i + D i) n =
      ∑ k ∈ Finset.range (n + 1), degreeTerm C D n k := by
  rw [orderedProduct_add_expansion, Finset.sum_powerset]
  simp [degreeTerm]

/--
Exact identity `degreeTerm C D n 0 = orderedProduct C n`.

Use: `chebyshev1.orderedProduct_add_decomposition` uses this identity to establish exact
identity `orderedProduct (fun i => C i + D i) n = orderedProduct C n + firstVariation C D n +
higherOrder C D n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem degreeTerm_zero [Semiring A] (C D : ℕ → A) (n : ℕ) :
    degreeTerm C D n 0 = orderedProduct C n := by simp [degreeTerm]

/--
Exact identity `degreeTerm C D n 1 = ∑ s ∈ Finset.range n, insertionTerm C D n {s}`.

Use: `chebyshev1.firstVariation_eq_sum` rewrites with this identity to establish exact
identity `firstVariation C D n = ∑ s ∈ Finset.range n, orderedProduct (fun i => C (s + 1 + i))
(n - (s + 1)) * D s * orderedProduct C s`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem degreeTerm_one [Semiring A] (C D : ℕ → A) (n : ℕ) :
    degreeTerm C D n 1 = ∑ s ∈ Finset.range n, insertionTerm C D n {s} := by simp [degreeTerm, Finset.powersetCard_one]

/--
Exact identity `degreeTerm C D n k = 0`.

Use: `chebyshev1.JacobiData.driftOrder_eq_zero` rewrites with this identity to establish
exact identity `J.driftOrder I N k H E = 0`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem degreeTerm_eq_zero_of_lt [Semiring A] (C D : ℕ → A) {n k : ℕ}
    (h : n < k) : degreeTerm C D n k = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  have := Finset.card_le_card hsub
  simp only [Finset.card_range, hcard] at this
  omega

/--
A single insertion has the unperturbed tail on its left and prefix on its right.

Exact identity `insertionTerm C D n {s} = orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1))
* D s * orderedProduct C s`.

Use: `chebyshev1.firstVariation_eq_sum` uses this identity to establish the identity
`firstVariation C D n = ∑ s ∈ Finset.range n, orderedProduct (fun i => C (s + 1 + i)) (n - (s +
1)) * D s * orderedProduct C s`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_add`,
`chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the arguments
shown in the proof.
-/
theorem insertionTerm_singleton [Monoid A] (C D : ℕ → A) {n s : ℕ} (hs : s < n) :
    insertionTerm C D n {s} =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) *
        D s * orderedProduct C s := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_add`,
  -- `chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the
  -- arguments shown in the proof.
  unfold insertionTerm
  rw [show n = (s + 1) + (n - (s + 1)) by omega, orderedProduct_add,
    orderedProduct_succ]
  have htail : orderedProduct
      (fun i => if s + 1 + i ∈ ({s} : Finset ℕ) then D (s + 1 + i)
        else C (s + 1 + i)) (n - (s + 1)) =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) := by
    apply orderedProduct_congr
    intro i _
    simp [show s + 1 + i ≠ s by omega]
  have hprefix : orderedProduct (fun i => if i ∈ ({s} : Finset ℕ) then D i else C i) s =
      orderedProduct C s := by
    apply orderedProduct_congr
    intro i hi
    simp [show i ≠ s by omega]
  rw [htail, hprefix]
  simp [mul_assoc]

/--
Peel off the latest insertion, leaving an unperturbed tail.

Exact identity `insertionTerm C D n (insert s S) = orderedProduct (fun i => C (s + 1 + i)) (n -
(s + 1)) * D s * insertionTerm C D s S`.

Use: `chebyshev1.JacobiData.insertionTerm_blocks` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_add`,
`chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the arguments
shown in the proof.
-/
theorem insertionTerm_insert_max [Monoid A] (C D : ℕ → A) {n s : ℕ}
    (hs : s < n) (S : Finset ℕ) (hS : S ⊆ Finset.range s) :
    insertionTerm C D n (insert s S) =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) * D s * insertionTerm C D s S := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_add`,
  -- `chebyshev1.orderedProduct_succ`, `chebyshev1.orderedProduct_congr` with the
  -- arguments shown in the proof.
  unfold insertionTerm
  rw [show n = (s + 1) + (n - (s + 1)) by omega, orderedProduct_add, orderedProduct_succ]
  simp only [Finset.mem_insert_self, ite_true]
  have ht : orderedProduct (fun i => if s + 1 + i ∈ insert s S then D (s + 1 + i)
      else C (s + 1 + i)) (n - (s + 1)) =
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) := by
    apply orderedProduct_congr
    intro i _
    have hni : s + 1 + i ∉ S := by intro hi; have := Finset.mem_range.mp (hS hi); omega
    simp [hni, show s + 1 + i ≠ s by omega]
  have hp : orderedProduct (fun i => if i ∈ insert s S then D i else C i) s =
      orderedProduct (fun i => if i ∈ S then D i else C i) s := by
    apply orderedProduct_congr
    intro i hi
    simp [show i ≠ s by omega]
  rw [ht, hp, mul_assoc]
  simp only [Nat.add_sub_cancel_left]

/--
A time-ordered block product, indexed by insertion times in decreasing order.

Use: `chebyshev1.JacobiData.blockWord_bound_nonneg` rewrites with this definition to
establish the stated quantitative bound `0 ≤ blockWord J.blockBound (fun _ => 1) n times`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def blockWord [Monoid A] (B : ℕ → ℕ → A) (E : ℕ → A) : ℕ → List ℕ → A
  | n, [] => B 0 n
  | n, s :: times => B (s + 1) (n - (s + 1)) * E s * blockWord B E s times

/--
The first-order part, before any input/output contraction.

Use: `chebyshev1.firstVariation_eq_sum` rewrites with this definition to establish exact
identity `firstVariation C D n = ∑ s ∈ Finset.range n, orderedProduct (fun i => C (s + 1 + i))
(n - (s + 1)) * D s * orderedProduct C s`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def firstVariation [Semiring A] (C D : ℕ → A) (n : ℕ) : A := degreeTerm C D n 1

/--
Exact identity `firstVariation C D n = ∑ s ∈ Finset.range n, orderedProduct (fun i => C (s + 1
+ i)) (n - (s + 1)) * D s * orderedProduct C s`.

Use: `chebyshev1.Realization.linearResponse_eq_sum` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem firstVariation_eq_sum [Semiring A] (C D : ℕ → A) (n : ℕ) :
    firstVariation C D n = ∑ s ∈ Finset.range n,
      orderedProduct (fun i => C (s + 1 + i)) (n - (s + 1)) *
        D s * orderedProduct C s := by
  rw [firstVariation, degreeTerm_one]
  apply Finset.sum_congr rfl
  intro s hs
  exact insertionTerm_singleton C D (Finset.mem_range.mp hs)

/--
Exact identity `firstVariation C D 0 = 0`.

Use: `chebyshev1.orderedProduct_add_decomposition` uses this identity to establish exact
identity `orderedProduct (fun i => C i + D i) n = orderedProduct C n + firstVariation C D n +
higherOrder C D n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.degreeTerm_one` with the arguments shown in
the proof.
-/
@[simp] theorem firstVariation_zero [Semiring A] (C D : ℕ → A) :
    firstVariation C D 0 = 0 := by simp [firstVariation, degreeTerm_one]

/--
Exact identity `firstVariation C D (n + 1) = D n * orderedProduct C n + C n * firstVariation C
D n`.

Use: `chebyshev1.hasDerivAt_orderedProduct_affine` rewrites with this identity to establish
the actual derivative at the stated point: `HasDerivAt (fun δ : ℝ => orderedProduct (fun s => C
s + δ • D s) n) (firstVariation C D n) 0`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem firstVariation_succ [Semiring A] (C D : ℕ → A) (n : ℕ) :
    firstVariation C D (n + 1) =
      D n * orderedProduct C n + C n * firstVariation C D n := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  simp only [firstVariation, degreeTerm_one, Finset.sum_range_succ]
  rw [Finset.mul_sum, add_comm]
  congr 1
  · simpa using insertionTerm_singleton C D (show n < n + 1 by omega)
  · apply Finset.sum_congr rfl
    intro s hs
    have hns : n ≠ s := by have := Finset.mem_range.mp hs; omega
    simp [insertionTerm, hns]

/--
Contributions of orders two through `n`, including the empty sum for `n ≤ 1`.

Use: `chebyshev1.orderedProduct_add_decomposition` rewrites with this definition to
establish exact identity `orderedProduct (fun i => C i + D i) n = orderedProduct C n +
firstVariation C D n + higherOrder C D n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_le`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.
-/
def higherOrder [Semiring A] (C D : ℕ → A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range (n - 1), degreeTerm C D n (k + 2)

/--
Exact constant + linear + higher-order decomposition (algebraic Proposition 1.3).

Exact identity `orderedProduct (fun i => C i + D i) n = orderedProduct C n + firstVariation C D
n + higherOrder C D n`.

Use: `chebyshev1.Realization.operatorTransfer_decomposition` rewrites with this identity to
establish exact identity `R.operatorTransfer n (fun s => H + E s) = R.operatorTransfer n (fun _
=> H) + R.linearResponse n H E + R.driftRemainder n H E`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.static_shift_attained`.

Source: mathlib, Mathlib.Algebra.Ring.Defs — distributive subset expansion of a noncommutative
finite product.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_add_by_degree` with the
arguments shown in the proof.
-/
theorem orderedProduct_add_decomposition [Semiring A] (C D : ℕ → A) (n : ℕ) :
    orderedProduct (fun i => C i + D i) n =
      orderedProduct C n + firstVariation C D n + higherOrder C D n := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_add_by_degree` with the
  -- arguments shown in the proof.
  cases n with
  | zero => simp [higherOrder]
  | succ n =>
    rw [orderedProduct_add_by_degree]
    rw [show n + 1 + 1 = 2 + n by omega, Finset.sum_range_add]
    simp [Finset.sum_range_succ, firstVariation, higherOrder, Nat.add_comm]

end chebyshev1

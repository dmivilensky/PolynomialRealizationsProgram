import «2610.05164v2».Continuum.NuclearSeries

/-!
Article: 2610.05164v2, Theorem 2.4.
Sorting and zero padding preserve the complete trace, including finite rank.
Use: `«2610.05164v2».Continuum.spectralSorted_tsum` feeds
`«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_tsum` (eigenvalue tsum).
Proof chain: `«2610.05164v2».Packing.packedKernel_hasSum_square_trace` — 2610.05164v2, Theorem 2.4;
Uniform l1 spectral transfer, ground parameter and Fredholm/cosh observations.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Set Filter
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} {a : ι → ℝ}

/--
The stated quantitative bound `{i | ε ≤ a i}.Finite`.

Use: `«2610.05164v2».Continuum.positive_maximum_outside` uses this bound to establish
constructs witnesses with the exact properties `∃ i, i ∉ s ∧ 0 < a i ∧ ∀ j, j ∉ s → a j ≤ a i`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem summable_superlevel_finite (hs : Summable a) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ a i}.Finite := by
  have h := hs.tendsto_cofinite_zero.eventually (eventually_lt_nhds hε)
  simpa only [mem_ofPred_eq, not_lt] using (Filter.eventually_cofinite.mp h)

/--
Constructs witnesses with the exact properties `∃ i, i ∉ s ∧ 0 < a i ∧ ∀ j, j ∉ s → a j ≤ a i`.

Use: `«2610.05164v2».Continuum.spectralNext` uses this bound in the displayed construction of
`spectralNext`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Separate `a i ≤ a k` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem positive_maximum_outside (hs : Summable a) (s : Finset ι)
    (h : ∃ i, i ∉ s ∧ 0 < a i) :
    ∃ i, i ∉ s ∧ 0 < a i ∧ ∀ j, j ∉ s → a j ≤ a i := by
  -- Separate `a i ≤ a k` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  classical
  obtain ⟨i,his,hi⟩ := h
  let t : Set ι := {j | a i ≤ a j ∧ j ∉ s}
  have ht : t.Finite := (summable_superlevel_finite hs hi).subset (fun _ h => h.1)
  have htn : t.Nonempty := ⟨i,le_rfl,his⟩
  obtain ⟨j,hjt,hmax⟩ := ht.toFinset.exists_max_image a (by simpa using htn)
  have hjt' : j ∈ t := ht.mem_toFinset.mp hjt
  refine ⟨j,hjt'.2,hi.trans_le hjt'.1,?_⟩
  intro k hks
  by_cases hk : a i ≤ a k
  · exact hmax k (ht.mem_toFinset.mpr ⟨hk,hks⟩)
  · exact (lt_of_not_ge hk).le.trans hjt'.1

/--
Select the greatest remaining positive coefficient; None means exhaustion.

Use: `«2610.05164v2».Continuum.spectralNext_none` uses this definition to establish establishes
the uniform, quantified assertion `∀ i, i ∉ s → a i ≤ 0`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def spectralNext (hs : Summable a) (s : Finset ι) : Option ι :=
  if h : ∃ i, i ∉ s ∧ 0 < a i then some (positive_maximum_outside hs s h).choose else none

/--
Defines `spectralSelected` by pattern matching with result type `ℕ → Finset ι`. The displayed
branches determine the recursive cases and their returned values.

Use: `«2610.05164v2».Continuum.spectralSelected_card_le` rewrites with this definition to
establish the stated quantitative bound `(spectralSelected hs n).card ≤ n`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def spectralSelected (hs : Summable a) : ℕ → Finset ι
  | 0 => ∅
  | n+1 => match spectralNext hs (spectralSelected hs n) with
      | none => spectralSelected hs n
      | some i => insert i (spectralSelected hs n)

/--
Nonincreasing eigenvalue listing with zero padding after exhaustion.

Use: `«2610.05164v2».Continuum.spectralSelected_ge_last` uses this definition to establish the
stated quantitative bound `spectralSorted hs n ≤ a i`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.
-/
def spectralSorted (hs : Summable a) (n : ℕ) : ℝ :=
  (spectralNext hs (spectralSelected hs n)).elim 0 a

/--
The stated quantitative bound `i ∉ s ∧ 0 < a i ∧ ∀ j, j ∉ s → a j ≤ a i`.

Use: `«2610.05164v2».Continuum.spectralSelected_card_le` rewrites with this bound to establish
the stated quantitative bound `(spectralSelected hs n).card ≤ n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.positive_maximum_outside` with
the arguments shown in the proof.
-/
theorem spectralNext_some (hs : Summable a) {s : Finset ι} {i : ι}
    (h : spectralNext hs s = some i) : i ∉ s ∧ 0 < a i ∧ ∀ j, j ∉ s → a j ≤ a i := by
  unfold spectralNext at h
  split_ifs at h with hp
  · have he : (positive_maximum_outside hs s hp).choose = i := Option.some.inj h
    exact he ▸ (positive_maximum_outside hs s hp).choose_spec

/--
Establishes the uniform, quantified assertion `∀ i, i ∉ s → a i ≤ 0`.

Use: `«2610.05164v2».Continuum.spectralSelected_card_of_missing` uses this bound to establish
exact identity `(spectralSelected hs n).card = n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem spectralNext_none (hs : Summable a) {s : Finset ι} (h : spectralNext hs s = none) :
    ∀ i, i ∉ s → a i ≤ 0 := by
  unfold spectralNext at h
  split_ifs at h with hp
  intro i hi
  exact le_of_not_gt (fun ha => hp ⟨i,hi,ha⟩)

/--
The precise assertion is `spectralSelected hs n ⊆ spectralSelected hs (n+1)`.

Use: `«2610.05164v2».Continuum.spectralSelected_card_of_missing` uses this assertion to
establish exact identity `(spectralSelected hs n).card = n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem spectralSelected_mono_step (hs : Summable a) (n : ℕ) :
    spectralSelected hs n ⊆ spectralSelected hs (n+1) := by
  classical
  rw [spectralSelected]
  split <;> simp

/--
Monotonicity in increasing order: `Monotone (spectralSelected hs)`.

Use: `«2610.05164v2».Continuum.spectralSelected_contains_finite` uses this assertion to
establish constructs witnesses with the exact properties `∃ n, ∀ i ∈ s, 0 < a i → i ∈
spectralSelected hs n`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSelected_mono_step` with
the arguments shown in the proof.
-/
theorem spectralSelected_mono (hs : Summable a) : Monotone (spectralSelected hs) :=
  monotone_nat_of_le_succ (spectralSelected_mono_step hs)

/--
The stated quantitative bound `(spectralSelected hs n).card ≤ n`.

Use: `«2610.05164v2».Continuum.eigenvalue_ge_of_eigenframe` uses this bound to establish the
stated quantitative bound `r ≤ D.eigenvalue n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_card_le (hs : Summable a) (n : ℕ) : (spectralSelected hs n).card ≤ n := by
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    rw [spectralSelected]
    cases h : spectralNext hs (spectralSelected hs n) with
    | none => exact ih.trans (Nat.le_succ n)
    | some i => rw [Finset.card_insert_of_notMem (spectralNext_some hs h).1]; omega

/--
The stated quantitative bound `0 ≤ spectralSorted hs n`.

Use: `«2610.05164v2».Continuum.spectralSorted_antitone` uses this bound to establish
monotonicity in decreasing order: `Antitone (spectralSorted hs)`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralNext_some` with the
arguments shown in the proof.
-/
theorem spectralSorted_nonneg (hs : Summable a) (n : ℕ) : 0 ≤ spectralSorted hs n := by
  unfold spectralSorted
  cases h : spectralNext hs (spectralSelected hs n) with
  | none => exact le_rfl
  | some i => exact (spectralNext_some hs h).2.1.le

/--
Exact identity `spectralSorted hs n = a i`.

Use: `«2610.05164v2».Continuum.spectralSelected_ge_last` rewrites with this identity to
establish the stated quantitative bound `spectralSorted hs n ≤ a i`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem spectralSorted_eq (hs : Summable a) {n : ℕ} {i : ι}
    (h : spectralNext hs (spectralSelected hs n) = some i) : spectralSorted hs n = a i := by simp only [spectralSorted,h,Option.elim_some]

/--
The stated quantitative bound `a i ≤ spectralSorted hs n`.

Use: `«2610.05164v2».Continuum.spectralSorted_antitone` uses this bound to establish
monotonicity in decreasing order: `Antitone (spectralSorted hs)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralNext_none`,
`«2610.05164v2».Continuum.spectralNext_some` with the arguments shown in the proof.
-/
theorem spectralSorted_max (hs : Summable a) (n : ℕ) {i : ι}
    (hi : i ∉ spectralSelected hs n) : a i ≤ spectralSorted hs n := by
  unfold spectralSorted
  cases h : spectralNext hs (spectralSelected hs n) with
  | none => exact spectralNext_none hs h i hi
  | some j => exact (spectralNext_some hs h).2.2 i hi

/--
Monotonicity in decreasing order: `Antitone (spectralSorted hs)`.

Use: `«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_antitone` uses this assertion to
establish monotonicity in decreasing order: `Antitone D.eigenvalue`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_nonneg`,
`«2610.05164v2».Continuum.spectralSorted_eq`, `«2610.05164v2».Continuum.spectralSorted_max`
with the arguments shown in the proof.
-/
theorem spectralSorted_antitone (hs : Summable a) : Antitone (spectralSorted hs) := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_nonneg`,
  -- `«2610.05164v2».Continuum.spectralSorted_eq`,
  -- `«2610.05164v2».Continuum.spectralSorted_max` with the arguments shown in the proof.
  apply antitone_nat_of_succ_le
  intro n
  cases h : spectralNext hs (spectralSelected hs (n+1)) with
  | none => simpa only [spectralSorted,h,Option.elim_none] using spectralSorted_nonneg hs n
  | some i =>
    rw [spectralSorted_eq hs h]
    apply spectralSorted_max
    exact fun hi => (spectralNext_some hs h).1 (spectralSelected_mono_step hs n hi)

/--
Establishes the uniform, quantified assertion `∀ i ∈ spectralSelected hs n, 0 < a i`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.4.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_positive (hs : Summable a) (n : ℕ) :
    ∀ i ∈ spectralSelected hs n, 0 < a i := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  classical
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    rw [spectralSelected]
    cases h : spectralNext hs (spectralSelected hs n) with
    | none => exact ih
    | some i =>
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (spectralNext_some hs h).2.1
      · exact ih j hj

/--
Exact identity `(∑ i ∈ spectralSelected hs n, a i) = ∑ j ∈ Finset.range n, spectralSorted hs
j`.

Use: `«2610.05164v2».Continuum.spectralSorted_summable` rewrites with this identity to
establish summability of the displayed sequence: `Summable (spectralSorted hs)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_sum (hs : Summable a) (n : ℕ) :
    (∑ i ∈ spectralSelected hs n, a i) = ∑ j ∈ Finset.range n, spectralSorted hs j := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  classical
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    rw [Finset.sum_range_succ,spectralSelected]
    cases h : spectralNext hs (spectralSelected hs n) with
    | none => simp only [ih,spectralSorted,h,Option.elim_none,add_zero]
    | some i =>
      rw [Finset.sum_insert (spectralNext_some hs h).1,ih,spectralSorted_eq hs h]
      exact add_comm _ _


/--
Establishes the uniform, quantified assertion `∀ j ∈ spectralSelected hs n, a i ≤ a j`.

Use: `«2610.05164v2».Continuum.spectralSelected_exhausts` uses this bound to establish
constructs witnesses with the exact properties `∃ n, i ∈ spectralSelected hs n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_ge_missing (hs : Summable a) (n : ℕ) {i : ι}
    (hi : i ∉ spectralSelected hs n) : ∀ j ∈ spectralSelected hs n, a i ≤ a j := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    rw [spectralSelected] at hi ⊢
    cases h : spectralNext hs (spectralSelected hs n) with
    | none =>
      simp only [h] at hi
      exact ih hi
    | some k =>
      simp only [h] at hi
      have hin : i ∉ spectralSelected hs n := fun hh => hi (Finset.mem_insert_of_mem hh)
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (spectralNext_some hs h).2.2 i hin
      · exact ih hin j hj

/--
The stated quantitative bound `spectralSorted hs n ≤ a i`.

Use: `«2610.05164v2».Continuum.gram_eigenvalue_le` uses this bound to establish the stated
quantitative bound `D.eigenvalue n ≤ D'.eigenvalue n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_eq`,
`«2610.05164v2».Continuum.spectralSelected_ge_missing`,
`«2610.05164v2».Continuum.spectralNext_some` with the arguments shown in the proof.
-/
theorem spectralSelected_ge_last (hs : Summable a) (hn : ∀ i, 0 ≤ a i) (n : ℕ)
    {i : ι} (hi : i ∈ spectralSelected hs (n+1)) : spectralSorted hs n ≤ a i := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_eq`,
  -- `«2610.05164v2».Continuum.spectralSelected_ge_missing`,
  -- `«2610.05164v2».Continuum.spectralNext_some` with the arguments shown in the proof.
  cases h : spectralNext hs (spectralSelected hs n) with
  | none => simpa only [spectralSorted,h,Option.elim_none] using hn i
  | some j =>
    rw [spectralSorted_eq hs h]
    rw [spectralSelected,h] at hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact le_rfl
    · exact spectralSelected_ge_missing hs n (spectralNext_some hs h).1 i hi

/--
Exact identity `(spectralSelected hs n).card = n`.

Use: `«2610.05164v2».Continuum.spectralSelected_exhausts` uses this identity to establish
constructs witnesses with the exact properties `∃ n, i ∈ spectralSelected hs n`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem spectralSelected_card_of_missing (hs : Summable a) (n : ℕ) {i : ι}
    (hi : i ∉ spectralSelected hs n) (hp : 0 < a i) : (spectralSelected hs n).card = n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp [spectralSelected]
  | succ n ih =>
    have hin : i ∉ spectralSelected hs n := fun hh => hi (spectralSelected_mono_step hs n hh)
    rw [spectralSelected]
    cases h : spectralNext hs (spectralSelected hs n) with
    | none => exact (not_lt_of_ge (spectralNext_none hs h i hin) hp).elim
    | some k => rw [Finset.card_insert_of_notMem (spectralNext_some hs h).1, ih hin]

/--
Every positive coefficient is selected in finite time.

Constructs witnesses with the exact properties `∃ n, i ∈ spectralSelected hs n`.

Use: `«2610.05164v2».Continuum.spectralSelected_contains_finite` uses this assertion to
establish constructs witnesses with the exact properties `∃ n, ∀ i ∈ s, 0 < a i → i ∈
spectralSelected hs n`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem spectralSelected_exhausts (hs : Summable a) (hn : ∀ i, 0 ≤ a i) {i : ι} (hp : 0 < a i) :
    ∃ n, i ∈ spectralSelected hs n := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  by_contra! hi
  obtain ⟨n,hn'⟩ := exists_nat_gt ((∑' j, a j) / a i)
  have hcard := spectralSelected_card_of_missing hs n (hi n) hp
  have hsum : (n : ℝ) * a i ≤ ∑' j, a j := by
    calc
      _ = ∑ j ∈ spectralSelected hs n, a i := by simp [hcard]
      _ ≤ ∑ j ∈ spectralSelected hs n, a j :=
        Finset.sum_le_sum (fun j hj => spectralSelected_ge_missing hs n (hi n) j hj)
      _ ≤ _ := hs.sum_le_tsum _ (fun j _ => hn j)
  exact not_lt_of_ge hsum ((div_lt_iff₀ hp).mp hn')

/--
Summability of the displayed sequence: `Summable (spectralSorted hs)`.

Use: `«2610.05164v2».Continuum.spectralSorted_tsum` uses this summability result to establish
exact identity `(∑' n, spectralSorted hs n) = ∑' i, a i`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_nonneg`,
`«2610.05164v2».Continuum.spectralSelected_sum` with the arguments shown in the proof.
-/
theorem spectralSorted_summable (hs : Summable a) (hn : ∀ i, 0 ≤ a i) :
    Summable (spectralSorted hs) := by
  apply summable_of_sum_range_le (spectralSorted_nonneg hs)
  intro n
  rw [← spectralSelected_sum]
  exact hs.sum_le_tsum _ (fun i _ => hn i)

/--
Constructs witnesses with the exact properties `∃ n, ∀ i ∈ s, 0 < a i → i ∈ spectralSelected hs
n`.

Use: `«2610.05164v2».Continuum.spectralSorted_tsum` uses this bound to establish the identity
`(∑' n, spectralSorted hs n) = ∑' i, a i`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Continuum.kernelEigenvalue_square_integral`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Induct on `s`; the recursive step uses the previous-stage assertion. Separate `0 < a i`
from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem spectralSelected_contains_finite (hs : Summable a) (hn : ∀ i, 0 ≤ a i) (s : Finset ι) :
    ∃ n, ∀ i ∈ s, 0 < a i → i ∈ spectralSelected hs n := by
  -- Induct on `s`; the recursive step uses the previous-stage assertion.
  induction s using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨n,hn'⟩ := ih
    by_cases hp : 0 < a i
    · obtain ⟨k,hk⟩ := spectralSelected_exhausts hs hn hp
      refine ⟨max n k, ?_⟩
      intro j hj hjp
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact spectralSelected_mono hs (le_max_right n k) hk
      · exact spectralSelected_mono hs (le_max_left n k) (hn' j hj hjp)
    · refine ⟨n,?_⟩
      intro j hj hjp
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hp hjp).elim
      · exact hn' j hj hjp

/--
Sorting and zero padding preserve the complete trace, including finite rank.

Exact identity `(∑' n, spectralSorted hs n) = ∑' i, a i`.

Use: `«2610.05164v2».Continuum.PositiveSpectralData.eigenvalue_tsum` uses this identity to
establish exact identity `(∑' n, D.eigenvalue n) = ∑' i, D.eig i`.

Article: 2610.05164v2, Theorem 2.4 via
`«2610.05164v2».Packing.packedKernel_hasSum_square_trace`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_summable`,
`«2610.05164v2».Continuum.spectralSorted_nonneg`,
`«2610.05164v2».Continuum.spectralSelected_sum` with the arguments shown in the proof.
-/
theorem spectralSorted_tsum (hs : Summable a) (hn : ∀ i, 0 ≤ a i) :
    (∑' n, spectralSorted hs n) = ∑' i, a i := by
  -- Use the identities/estimates `«2610.05164v2».Continuum.spectralSorted_summable`,
  -- `«2610.05164v2».Continuum.spectralSorted_nonneg`,
  -- `«2610.05164v2».Continuum.spectralSelected_sum` with the arguments shown in the proof.
  have hsorted := spectralSorted_summable hs hn
  apply le_antisymm
  · apply Real.tsum_le_of_sum_range_le (spectralSorted_nonneg hs)
    intro n
    rw [← spectralSelected_sum]
    exact hs.sum_le_tsum _ (fun i _ => hn i)
  · apply Real.tsum_le_of_sum_le hn
    intro s
    obtain ⟨n,hcover⟩ := spectralSelected_contains_finite hs hn s
    let t := s.filter (fun i => 0 < a i)
    have he : (∑ i ∈ s, a i) = ∑ i ∈ t, a i := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hit
      have hp : ¬0 < a i := fun hp => hit (Finset.mem_filter.mpr ⟨hi,hp⟩)
      exact le_antisymm (le_of_not_gt hp) (hn i)
    have ht : t ⊆ spectralSelected hs n := by
      intro i hi
      obtain ⟨his,hip⟩ := Finset.mem_filter.mp hi
      exact hcover i his hip
    rw [he]
    calc
      _ ≤ ∑ i ∈ spectralSelected hs n, a i :=
        Finset.sum_le_sum_of_subset_of_nonneg ht (fun i _ _ => hn i)
      _ = ∑ j ∈ Finset.range n, spectralSorted hs j := spectralSelected_sum hs n
      _ ≤ _ := hsorted.sum_le_tsum _ (fun j _ => spectralSorted_nonneg hs j)

end
end «2610.05164v2».Continuum

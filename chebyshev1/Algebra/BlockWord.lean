import chebyshev1.Algebra.OrderedProduct
import Mathlib.Data.Finset.Sort

/-!
Article: chebyshev1, Theorem 4.3.
Scaling every surviving site scales a word by exactly its number of surviving sites.
Use: `chebyshev1.blockWord_scale` feeds `chebyshev1.JacobiData.normalizedOperatorWord_eq`
(normalized Operator Word eq).
Proof chain: `chebyshev1.JacobiData.driftOrder_normalized` — chebyshev1, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace chebyshev1
open scoped BigOperators

/--
Descending insertion times, all strictly inside the current prefix.

Use: `chebyshev1.wordValid_sort` rewrites with this definition to establish the stated
quantitative bound `WordValid n (times.sort (· ≥ ·))`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.
-/
def WordValid : ℕ → List ℕ → Prop
  | _, [] => True
  | n, s :: times => s < n ∧ WordValid s times

/--
The stated quantitative bound `times.length ≤ n`.

Use: `chebyshev1.blockWord_scale` uses this bound to establish the identity `blockWord
(fun a k => c^k • B a k) E n times = c^(n-times.length) • blockWord B E n times`.

Article: chebyshev1, Theorem 4.3 via `chebyshev1.JacobiData.driftOrder_normalized`.

Proof: Induct on `times` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem WordValid.length_le {n : ℕ} {times : List ℕ} (h : WordValid n times) :
    times.length ≤ n := by
  -- Induct on `times` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction times generalizing n with
  | nil => simp
  | cons s times ih =>
    have hl := ih h.2
    have hs := h.1
    simp only [List.length_cons]
    omega

/--
The stated quantitative bound `WordValid n (times.sort (· ≥ ·))`.

Use: `chebyshev1.JacobiData.endpointWeight_eq_partitionWeight` uses this bound to establish
exact identity `J.endpointWeight n times = J.partitionWeight n times`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Induct on `times`; the recursive step uses the previous-stage assertion. Separate `times
= ∅` from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem wordValid_sort (n : ℕ) (times : Finset ℕ) (ht : times ⊆ Finset.range n) :
    WordValid n (times.sort (· ≥ ·)) := by
  -- Induct on `times`; the recursive step uses the previous-stage assertion.
  induction times using Finset.strongInductionOn generalizing n with
  | _ times ih =>
    by_cases hz : times = ∅
    · subst times; simp [WordValid]
    · have hne := Finset.nonempty_iff_ne_empty.mpr hz
      let s := times.max' hne
      have hmem : s ∈ times := times.max'_mem hne
      have hs : s < n := Finset.mem_range.mp (ht hmem)
      have hsub : times.erase s ⊆ Finset.range s := by
        intro t ht'
        have hle : t ≤ s := times.le_max' t (Finset.mem_of_mem_erase ht')
        have hne' : t ≠ s := (Finset.mem_erase.mp ht').1
        exact Finset.mem_range.mpr (by omega)
      have he : insert s (times.erase s) = times := Finset.insert_erase hmem
      have hsort : times.sort (· ≥ ·) = s :: (times.erase s).sort (· ≥ ·) :=
        (congrArg (fun t : Finset ℕ => t.sort (· ≥ ·)) he.symm).trans
          (Finset.sort_insert (· ≥ ·) (fun t ht' => by
            have := Finset.mem_range.mp (hsub ht'); omega) (Finset.notMem_erase s times))
      rw [hsort]
      exact ⟨hs, ih _ (Finset.erase_ssubset hmem) s hsub⟩

/--
Exact identity `blockWord B E n times = blockWord B' E n times`.

Use: `chebyshev1.JacobiData.endpointWeight_eq_partitionWeight` uses this identity to
establish exact identity `J.endpointWeight n times = J.partitionWeight n times`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Induct on `times` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem blockWord_congr {A : Type*} [Monoid A] {N n : ℕ} {times : List ℕ}
    (B B' : ℕ → ℕ → A) (E : ℕ → A) (hn : n ≤ N) (ht : WordValid n times)
    (hB : ∀ a k, a+k ≤ N → B a k = B' a k) :
    blockWord B E n times = blockWord B' E n times := by
  -- Induct on `times` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction times generalizing n with
  | nil => exact hB 0 n (by simpa using hn)
  | cons s times ih =>
    simp only [blockWord]
    rw [hB (s+1) (n-(s+1)) (by have := ht.1; omega), ih (by have := ht.1; omega) ht.2]

/--
Scaling every surviving site scales a word by exactly its number of surviving sites.

Exact identity `blockWord (fun a k => c^k • B a k) E n times = c^(n-times.length) • blockWord B
E n times`.

Use: `chebyshev1.JacobiData.normalizedOperatorWord_eq` uses this identity to establish
exact identity `J.normalizedOperatorWord I H E N times = (2:ℝ)^(N-times.card) • J.operatorWord
I H E N times`.

Article: chebyshev1, Theorem 4.3 via `chebyshev1.JacobiData.driftOrder_normalized`.

Proof: Induct on `times` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem blockWord_scale {A : Type*} [Monoid A] [MulAction ℝ A] [SMulCommClass ℝ A A]
    [IsScalarTower ℝ A A] (B : ℕ → ℕ → A) (E : ℕ → A)
    (c : ℝ) {n : ℕ} {times : List ℕ} (ht : WordValid n times) :
    blockWord (fun a k => c^k • B a k) E n times =
      c^(n-times.length) • blockWord B E n times := by
  -- Induct on `times` while keeping `n` arbitrary; the recursive step uses the
  -- previous-stage assertion.
  induction times generalizing n with
  | nil => simp [blockWord]
  | cons s times ih =>
    simp only [blockWord, ih ht.2, smul_mul_assoc, mul_smul_comm, smul_smul,
      List.length_cons]
    rw [← pow_add]
    congr 2
    have hl := ht.2.length_le
    have hs := ht.1
    omega

end chebyshev1

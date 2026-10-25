import chebyshev1.Jacobi.OperatorTail
import Mathlib.Data.Finset.Sort

/-!
Article: chebyshev1, Theorem 4.3.
Exact expansion over every insertion order, with the actual realization as the output.
Use: `chebyshev1.JacobiData.finiteDrift_words` feeds
`chebyshev1.JacobiData.taylor_leading_partition` (The insertion coefficients are exactly the
Taylor coefficients of the terminal continuant).
Proof chain: `chebyshev1.JacobiData.opNorm_driftOrder_static` — chebyshev1, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
variable (J : JacobiData) (I : SpectralInterval)
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
Defines `operatorWord` of type `Matrix d d ℝ` by `blockWord (fun a k => aeval H
(J.spectralBlock I a k)) E n (times.sort (· ≥ ·))`.

Use: `chebyshev1.JacobiData.insertionTerm_blocks` rewrites with this definition to
establish the identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.
-/
def operatorWord (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) (n : ℕ) (times : Finset ℕ) :
    Matrix d d ℝ :=
  blockWord (fun a k => aeval H (J.spectralBlock I a k)) E n (times.sort (· ≥ ·))

/--
Exact identity `(T * (J.method I).memoryInsertion s E * P) 0 0 = (-(J.method I).gamma s) • (T 0
0 * E * P 0 0)`.

Use: `chebyshev1.JacobiData.insertionTerm_blocks` rewrites with this identity to establish
the identity stated in that declaration.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem memoryInsertion_contract (s : ℕ) (E : Matrix d d ℝ)
    (T P : Matrix (Fin 2) (Fin 2) (Matrix d d ℝ)) :
    (T * (J.method I).memoryInsertion s E * P) 0 0 =
      (-(J.method I).gamma s) • (T 0 0 * E * P 0 0) := by simp [TwoTerm.memoryInsertion, Matrix.mul_apply, Fin.sum_univ_two, neg_smul]

/--
Each time-ordered insertion has exactly the adjacent continuant blocks of 4.3(i).

Use: `chebyshev1.JacobiData.finiteDrift_words` uses this identity to establish exact
identity `(J.realization I).operatorTransfer N (fun s => H + E s) = ∑ times ∈ (Finset.range
N).powerset, ((-(2 / I.delta)) ^ times.card / J.den I N) • J.operatorWord I H E N times`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Induct on `times`; the recursive step uses the previous-stage assertion. Separate `times
= ∅` from its negation; prove the goal under each of these mutually exclusive hypotheses. Clear
the denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem insertionTerm_blocks {N : ℕ} (h : J.Admissible I N) (n : ℕ) (hn : n ≤ N)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) (times : Finset ℕ)
    (ht : times ⊆ Finset.range n) :
    (J.realization I).contract (insertionTerm (fun s => (J.realization I).operatorStep s H)
      (fun s => (J.realization I).operatorInsertion s (E s)) n times) =
      ((-(2 / I.delta)) ^ times.card / J.den I n) • J.operatorWord I H E n times := by
  -- Induct on `times`; the recursive step uses the previous-stage assertion.
  rw [realization, TwoTerm.insertionTerm_eq_memory]
  induction times using Finset.strongInductionOn generalizing n with
  | _ times ih =>
    by_cases hz : times = ∅
    · subst times
      simp only [insertionTerm_empty, Finset.card_empty, pow_zero, one_div,
        operatorWord, Finset.sort_empty, blockWord]
      exact J.operator_prefix I h n hn H
    · have hne := Finset.nonempty_iff_ne_empty.mpr hz
      let s := times.max' hne
      have hmem : s ∈ times := times.max'_mem hne
      have hs : s < n := Finset.mem_range.mp (ht hmem)
      have hsub : times.erase s ⊆ Finset.range s := by
        intro t ht'
        have hle : t ≤ s := times.le_max' t (Finset.mem_of_mem_erase ht')
        have hne' : t ≠ s := (Finset.mem_erase.mp ht').1
        exact Finset.mem_range.mpr (by omega)
      have hnot : s ∉ times.erase s := Finset.notMem_erase s times
      have hi := ih (times.erase s) (Finset.erase_ssubset hmem) s (by omega) hsub
      have he : insert s (times.erase s) = times := Finset.insert_erase hmem
      have hsort : times.sort (· ≥ ·) = s :: (times.erase s).sort (· ≥ ·) := by
        calc times.sort (· ≥ ·) = (insert s (times.erase s)).sort (· ≥ ·) :=
               congrArg (fun t : Finset ℕ => t.sort (· ≥ ·)) he.symm
             _ = _ := ?_
        exact Finset.sort_insert (· ≥ ·) (fun t ht' => by
          have := Finset.mem_range.mp (hsub ht'); omega) hnot
      have hcard : times.card = (times.erase s).card + 1 := by
        calc times.card = (insert s (times.erase s)).card := congrArg Finset.card he.symm
             _ = _ := Finset.card_insert_of_notMem hnot
      rw [← he, insertionTerm_insert_max _ _ hs _ hsub, J.memoryInsertion_contract I]
      have hsmall : J.Admissible I n := fun m hm => h m (hm.trans hn)
      rw [J.operator_tail I hsmall (s + 1) (by omega) (by omega) H, hi]
      rw [he]
      unfold operatorWord
      rw [hsort, blockWord]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      dsimp [method]
      rw [hcard, pow_succ]
      field_simp [J.den_ne I h (show s ≤ N by omega),
        J.den_ne I h (show s + 1 ≤ N by omega), J.den_ne I h hn]

/--
Exact expansion over every insertion order, with the actual realization as the output.

Exact identity `(J.realization I).operatorTransfer N (fun s => H + E s) = ∑ times ∈
(Finset.range N).powerset, ((-(2 / I.delta)) ^ times.card / J.den I N) • J.operatorWord I H E N
times`.

Use: `chebyshev1.JacobiData.taylor_leading_partition` uses this identity to establish exact
identity `taylor 1 (J.leading N) = ∑ times ∈ (Finset.range N).powerset, C (J.endpointWeight N
times) * X^times.card`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem finiteDrift_words {N : ℕ} (h : J.Admissible I N)
    (H : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) :
    (J.realization I).operatorTransfer N (fun s => H + E s) =
      ∑ times ∈ (Finset.range N).powerset,
        ((-(2 / I.delta)) ^ times.card / J.den I N) • J.operatorWord I H E N times := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [Realization.operatorTransfer_expansion]
  apply Finset.sum_congr rfl
  intro times ht
  exact J.insertionTerm_blocks I h N le_rfl H E times (Finset.mem_powerset.mp ht)

end
end chebyshev1.JacobiData

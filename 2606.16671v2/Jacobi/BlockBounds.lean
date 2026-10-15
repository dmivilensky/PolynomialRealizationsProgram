import «2606.16671v2».Jacobi.InsertionWords
import «2606.16671v2».Spectral.OperatorNorm
import Mathlib.Topology.Order.Compact

/-!
Article: 2606.16671v2, Theorem 4.3.
G_k from 4.3(ii): each surviving site contributes a factor two.
Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` feeds
`«2606.16671v2».JacobiData.opNorm_driftOrder_le` (op Norm drift Order le).
Proof chain: `«2606.16671v2».JacobiData.opNorm_driftOrder_G_le` — 2606.16671v2, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2».JacobiData
noncomputable section
open Polynomial
open scoped BigOperators
variable (J : JacobiData)

/--
Defines `blockValues` of type `Set ℝ` by `(fun x : ℝ => |(J.block a n).eval x|) '' Set.Icc (-1)
1`.

Use: `«2606.16671v2».JacobiData.blockBound` uses this definition in the displayed construction
of `blockBound`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def blockValues (a n : ℕ) : Set ℝ := (fun x : ℝ => |(J.block a n).eval x|) '' Set.Icc (-1) 1
/--
Defines `blockBound` of type `ℝ` by `sSup (J.blockValues a n)`.

Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` uses this definition to establish the
stated quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def blockBound (a n : ℕ) : ℝ := sSup (J.blockValues a n)

/--
The precise assertion is `IsCompact (J.blockValues a n)`.

Use: `«2606.16671v2».JacobiData.block_eval_le_bound` uses this assertion to establish the
stated quantitative bound `|(J.block a n).eval x| ≤ J.blockBound a n`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem blockValues_compact (a n : ℕ) : IsCompact (J.blockValues a n) :=
  isCompact_Icc.image (J.block a n).continuous.abs

/--
The precise assertion is `(J.blockValues a n).Nonempty`.

Use: `«2606.16671v2».JacobiData.blockBound_endpoint` uses this assertion to establish exact
identity `J.blockBound a n = (J.block a n).eval 1`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem blockValues_nonempty (a n : ℕ) : (J.blockValues a n).Nonempty :=
  ⟨_, 1, by norm_num, rfl⟩

/--
The stated quantitative bound `|(J.block a n).eval x| ≤ J.blockBound a n`.

Use: `«2606.16671v2».JacobiData.blockBound_endpoint` uses this bound to establish exact
identity `J.blockBound a n = (J.block a n).eval 1`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.blockValues_compact` with the
arguments shown in the proof.
-/
theorem block_eval_le_bound (a n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(J.block a n).eval x| ≤ J.blockBound a n :=
  le_csSup (J.blockValues_compact a n).bddAbove ⟨x, hx, rfl⟩

/--
The stated quantitative bound `0 ≤ J.blockBound a n`.

Use: `«2606.16671v2».JacobiData.blockWord_bound_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ blockWord J.blockBound (fun _ => 1) n times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.block_eval_le_bound` with the
arguments shown in the proof.
-/
theorem blockBound_nonneg (a n : ℕ) : 0 ≤ J.blockBound a n :=
  (abs_nonneg _).trans (J.block_eval_le_bound a n (x := 1) (by norm_num))

/--
Exact identity `J.blockBound a n = (J.block a n).eval 1`.

Use: `«2606.16671v2».JacobiData.endpointWeight_eq_partitionWeight` uses this identity to
establish exact identity `J.endpointWeight n times = J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.blockValues_nonempty`,
`«2606.16671v2».JacobiData.block_eval_le_bound` with the arguments shown in the proof.
-/
theorem blockBound_endpoint (a n : ℕ)
    (hm : ∀ x ∈ Set.Icc (-1) 1, |(J.block a n).eval x| ≤ (J.block a n).eval 1) :
    J.blockBound a n = (J.block a n).eval 1 := by
  -- Use the identities/estimates `«2606.16671v2».JacobiData.blockValues_nonempty`,
  -- `«2606.16671v2».JacobiData.block_eval_le_bound` with the arguments shown in the proof.
  have he : 0 ≤ (J.block a n).eval 1 := (abs_nonneg _).trans (hm 1 (by norm_num))
  apply le_antisymm
  · apply csSup_le (J.blockValues_nonempty a n)
    rintro _ ⟨x, hx, rfl⟩
    exact hm x hx
  · simpa only [abs_of_nonneg he] using J.block_eval_le_bound a n (x := 1) (by norm_num)

/--
Defines `partitionWeight` of type `ℝ` by `blockWord J.blockBound (fun _ => 1) n (times.sort (·
≥ ·))`.

Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` uses this definition to establish the
stated quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.
-/
def partitionWeight (n : ℕ) (times : Finset ℕ) : ℝ :=
  blockWord J.blockBound (fun _ => 1) n (times.sort (· ≥ ·))

/--
Defines `partitionBound` of type `ℝ` by `∑ times ∈ (Finset.range n).powersetCard k,
J.partitionWeight n times`.

Use: `«2606.16671v2».JacobiData.G` uses this definition in the displayed construction of `G`.
Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.
-/
def partitionBound (n k : ℕ) : ℝ :=
  ∑ times ∈ (Finset.range n).powersetCard k, J.partitionWeight n times

/--
G_k from 4.3(ii): each surviving site contributes a factor two.

Use: `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff` uses this definition to establish exact
identity `J.G N k = 2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.
-/
def G (n k : ℕ) : ℝ := (2 : ℝ) ^ (n - k) * J.partitionBound n k

/--
The stated quantitative bound `0 ≤ blockWord J.blockBound (fun _ => 1) n times`.

Use: `«2606.16671v2».JacobiData.opNorm_operatorWord_le` uses this identity to establish the
stated quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Article: 2606.16671v2, Corollary 5.3 via
`«2606.16671v2».SineJacobi.driftOrder_static_attained`.

Proof: Induct on `times` while keeping `n` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem blockWord_bound_nonneg (n : ℕ) (times : List ℕ) :
    0 ≤ blockWord J.blockBound (fun _ => 1) n times := by
  induction times generalizing n with
  | nil => exact J.blockBound_nonneg 0 n
  | cons s times ih =>
    simp only [blockWord, mul_one]
    exact mul_nonneg (J.blockBound_nonneg _ _) (ih s)

/--
The stated quantitative bound `opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card *
J.partitionWeight n times`.

Use: `«2606.16671v2».JacobiData.opNorm_driftOrder_le` uses this bound to establish the stated
quantitative bound `opNorm (J.driftOrder I N k H E) ≤ (2 / I.delta) ^ k / J.den I N * delta ^ k
* J.partitionBound N k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Induct on `times`; the recursive step uses the previous-stage assertion. Separate `times
= ∅` from its negation; prove the goal under each of these mutually exclusive hypotheses.
-/
theorem opNorm_operatorWord_le {d : Type*} [Fintype d] [DecidableEq d]
    (I : SpectralInterval) (N : ℕ) (H : Matrix d d ℝ) (hH : H.IsHermitian)
    (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L) (E : ℕ → Matrix d d ℝ)
    (delta : ℝ) (hd : 0 ≤ delta) (hE : ∀ s < N, opNorm (E s) ≤ delta)
    (n : ℕ) (hn : n ≤ N) (times : Finset ℕ) (ht : times ⊆ Finset.range n) :
    opNorm (J.operatorWord I H E n times) ≤ delta ^ times.card * J.partitionWeight n times := by
  -- Induct on `times`; the recursive step uses the previous-stage assertion.
  have hb (a k : ℕ) : opNorm (aeval H (J.spectralBlock I a k)) ≤ J.blockBound a k :=
    opNorm_aeval_le _ I H hH hspec _ (J.blockBound_nonneg a k)
      (fun x hx => by rw [spectralBlock_eval]; exact J.block_eval_le_bound a k (I.z_mem hx))
  induction times using Finset.strongInductionOn generalizing n with
  | _ times ih =>
    by_cases hz : times = ∅
    · subst times
      simpa [operatorWord, partitionWeight, blockWord] using hb 0 n
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
      have hsort : times.sort (· ≥ ·) = s :: (times.erase s).sort (· ≥ ·) :=
        (congrArg (fun t : Finset ℕ => t.sort (· ≥ ·)) he.symm).trans
          (Finset.sort_insert (· ≥ ·) (fun t ht' => by
            have := Finset.mem_range.mp (hsub ht'); omega) hnot)
      have hcard : times.card = (times.erase s).card + 1 :=
        (congrArg Finset.card he.symm).trans (Finset.card_insert_of_notMem hnot)
      unfold operatorWord partitionWeight
      rw [hsort, blockWord, blockWord, mul_one, hcard, pow_succ]
      have hpw : 0 ≤ J.partitionWeight s (times.erase s) := J.blockWord_bound_nonneg _ _
      calc
        _ ≤ (opNorm (aeval H (J.spectralBlock I (s + 1) (n - (s + 1)))) * opNorm (E s)) *
            opNorm (J.operatorWord I H E s (times.erase s)) :=
              (opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg _))
        _ ≤ (J.blockBound (s + 1) (n - (s + 1)) * delta) *
            (delta ^ (times.erase s).card * J.partitionWeight s (times.erase s)) :=
              mul_le_mul (mul_le_mul (hb _ _) (hE s (by omega)) (opNorm_nonneg _)
                (J.blockBound_nonneg _ _)) hi (opNorm_nonneg _)
                  (mul_nonneg (J.blockBound_nonneg _ _) hd)
        _ = _ := by unfold partitionWeight; ring

end
end «2606.16671v2».JacobiData

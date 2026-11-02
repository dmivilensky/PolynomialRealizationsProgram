import chebyshev2.Continuum.FiniteSorting

/-!
Sorting a positive finite spectrum with a strictly ordered initial segment.
Later eigenvalues may coincide. This permits the repeated minus-one roots
of the padded Nesterov polynomial without assuming a simple full spectrum.
Use: PaddedClosedSpectrum identifies every active resolvent coordinate;
the exact trace then controls the entire padded spectrum in l1.
Article: jacobi, Theorem 5.3.
Article role: the full repeated-root spectrum and its quarter-scaled l1 edge limit.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev2.Continuum
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Strict separation from every later entry fixes the initial sorted
segment, even when the unused tail has arbitrary multiplicities.
Article: jacobi, Theorem 5.3.
-/
theorem spectralSorted_prefix {M N : ℕ} (hMN : M≤N) {a : Fin N → ℝ}
    (ha : ∀ i j : Fin N,i.val < M → i < j → a j < a i)
    (hp : ∀ i,0<a i) (hs : Summable a) {n : ℕ} (hnM : n<M) :
    spectralSorted hs n=a ⟨n,hnM.trans_le hMN⟩ := by
  have hsel : ∀ n, n≤M → spectralSelected hs n = Finset.univ.filter (fun i : Fin N => i.val < n) := by
    intro n
    induction n with
    | zero => intro _; ext i; simp [spectralSelected]
    | succ n ih =>
      intro hnM
      have hn : n<N := lt_of_lt_of_le (by omega : n<M) hMN
      have ihn := ih (by omega : n≤M)
      · have hnot : (⟨n,hn⟩ : Fin N) ∉ spectralSelected hs n := by rw [ihn]; simp
        have hnext : spectralNext hs (spectralSelected hs n) = some ⟨n,hn⟩ := by
          cases he : spectralNext hs (spectralSelected hs n) with
          | none => exact (not_le_of_gt (hp ⟨n,hn⟩) (spectralNext_none hs he _ hnot)).elim
          | some i =>
            have hi := spectralNext_some hs he
            have hin : n ≤ i.val := by
              have hh := hi.1
              rw [ihn] at hh
              simpa using hh
            have hieq : i = ⟨n,hn⟩ := by
              apply Fin.ext
              change i.val = n
              by_contra hne
              have hlt : n < i.val := by omega
              exact (not_lt_of_ge (hi.2.2 ⟨n,hn⟩ hnot)) (ha _ _ (by change n < M; omega) hlt)
            simp only [hieq]
        rw [spectralSelected,hnext,ihn]
        ext i
        simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]
        constructor
        · rintro (h | h)
          · subst i; exact Nat.lt_succ_self n
          · omega
        · intro h
          by_cases hi : i.val = n
          · exact Or.inl (Fin.ext hi)
          · exact Or.inr (by omega)
  unfold spectralSorted
  have hn : n<N := hnM.trans_le hMN
  · have hnot : (⟨n,hn⟩ : Fin N) ∉ spectralSelected hs n := by rw [hsel n hnM.le]; simp
    cases he : spectralNext hs (spectralSelected hs n) with
    | none => exact (not_le_of_gt (hp ⟨n,hn⟩) (spectralNext_none hs he _ hnot)).elim
    | some i =>
      have hi := spectralNext_some hs he
      have hin : n ≤ i.val := by
        have hh := hi.1
        rw [hsel n hnM.le] at hh
        simpa using hh
      have hieq : i = ⟨n,hn⟩ := by
        apply Fin.ext
        change i.val = n
        by_contra hne
        have hlt : n < i.val := by omega
        exact (not_lt_of_ge (hi.2.2 ⟨n,hn⟩ hnot)) (ha _ _ hnM hlt)
      simp only [hieq,Option.elim_some]

end
end jacobi.Finite

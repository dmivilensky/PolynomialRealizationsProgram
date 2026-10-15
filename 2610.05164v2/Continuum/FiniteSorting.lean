import «2610.05164v2».Continuum.SpectralSorting

/-!
Article: 2610.05164v2, Theorem 2.3.
Sorting a strictly decreasing positive finite list preserves its order and adds exactly the
article's zero tail.
Use: `«2610.05164v2».Continuum.spectralSorted_fin` feeds
`«2610.05164v2».Continuum.green_eigenvalue_eq` (The ordered spectrum extracted from the actual Green
matrix is the explicit finite sequence used in Theorem 2.4).
Proof chain: `«2610.05164v2».Packing.packed_spectral_distance` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Continuum
noncomputable section
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/--
Sorting a strictly decreasing positive finite list preserves its order and adds exactly the
article's zero tail.

Exact identity `spectralSorted hs n = if h : n < N then a ⟨n,h⟩ else 0`.

Use: `«2610.05164v2».Continuum.green_eigenvalue_eq` uses this identity to establish exact
identity `(greenSpectralData J hN ht).eigenvalue = finiteEigenvalue N`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.packed_spectral_distance`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion. Separate `n < N`
from its negation; prove the goal under each of these mutually exclusive hypotheses. Assume the
failure of the desired conclusion and derive a contradiction from the available
bounds/identities.
-/
theorem spectralSorted_fin {N : ℕ} {a : Fin N → ℝ} (ha : StrictAnti a) (hp : ∀ i, 0 < a i)
    (hs : Summable a) (n : ℕ) :
    spectralSorted hs n = if h : n < N then a ⟨n,h⟩ else 0 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  have hsel : ∀ n, spectralSelected hs n = Finset.univ.filter (fun i : Fin N => i.val < n) := by
    intro n
    induction n with
    | zero => ext i; simp [spectralSelected]
    | succ n ih =>
      by_cases hn : n < N
      · have hnot : (⟨n,hn⟩ : Fin N) ∉ spectralSelected hs n := by rw [ih]; simp
        have hnext : spectralNext hs (spectralSelected hs n) = some ⟨n,hn⟩ := by
          cases he : spectralNext hs (spectralSelected hs n) with
          | none => exact (not_le_of_gt (hp ⟨n,hn⟩) (spectralNext_none hs he _ hnot)).elim
          | some i =>
            have hi := spectralNext_some hs he
            have hin : n ≤ i.val := by
              have hh := hi.1
              rw [ih] at hh
              simpa using hh
            have hieq : i = ⟨n,hn⟩ := by
              apply Fin.ext
              change i.val = n
              by_contra hne
              have hlt : n < i.val := by omega
              exact (not_lt_of_ge (hi.2.2 ⟨n,hn⟩ hnot)) (ha hlt)
            simp only [hieq]
        rw [spectralSelected,hnext,ih]
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
      · have hnext : spectralNext hs (spectralSelected hs n) = none := by
          cases he : spectralNext hs (spectralSelected hs n) with
          | none => rfl
          | some i =>
            have hi := (spectralNext_some hs he).1
            rw [ih] at hi
            have : i.val < n := by omega
            exact (hi (by simp [this])).elim
        rw [spectralSelected,hnext,ih]
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
        omega
  unfold spectralSorted
  by_cases hn : n < N
  · have hnot : (⟨n,hn⟩ : Fin N) ∉ spectralSelected hs n := by rw [hsel]; simp
    cases he : spectralNext hs (spectralSelected hs n) with
    | none => exact (not_le_of_gt (hp ⟨n,hn⟩) (spectralNext_none hs he _ hnot)).elim
    | some i =>
      have hi := spectralNext_some hs he
      have hin : n ≤ i.val := by
        have hh := hi.1
        rw [hsel] at hh
        simpa using hh
      have hieq : i = ⟨n,hn⟩ := by
        apply Fin.ext
        change i.val = n
        by_contra hne
        have hlt : n < i.val := by omega
        exact (not_lt_of_ge (hi.2.2 ⟨n,hn⟩ hnot)) (ha hlt)
      simp only [hieq,Option.elim_some,dite_eq_left hn]
  · cases he : spectralNext hs (spectralSelected hs n) with
    | none => simp only [Option.elim_none,dite_eq_right hn]
    | some i =>
      have hi := (spectralNext_some hs he).1
      rw [hsel] at hi
      have : i.val < n := by omega
      exact (hi (by simp [this])).elim

end
end «2610.05164v2».Continuum

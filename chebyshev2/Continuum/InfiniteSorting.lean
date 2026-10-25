import chebyshev2.Continuum.SpectralSorting

/-!
Article: chebyshev2, Proposition 2.
A positive strictly decreasing infinite list is unchanged by the actual spectral sorting
construction.
Use: `chebyshev2.Continuum.spectralSorted_nat` feeds
`chebyshev2.SineContinuum.sineSpectralData_eigenvalue` (sine Spectral Data eigenvalue).
Proof chain: `chebyshev2.SineContinuum.sine_kernel_eigenvalue` — chebyshev2, Proposition 2;
Sine coordinate bijection, symmetry, masses, spectrum, theta formula and tails.
-/
namespace chebyshev2.Continuum
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency true

/--
A positive strictly decreasing infinite list is unchanged by the actual spectral sorting
construction.

Exact identity `spectralSorted hs n=a n`.

Use: `chebyshev2.SineContinuum.sineSpectralData_eigenvalue` uses this identity to establish
exact identity `sineSpectralData.eigenvalue=Continuum.referenceEigenvalue`.

Article: chebyshev2, Proposition 2 via `chebyshev2.SineContinuum.sine_kernel_eigenvalue`.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion. Assume the failure
of the desired conclusion and derive a contradiction from the available bounds/identities.
-/
theorem spectralSorted_nat {a : ℕ → ℝ} (ha : StrictAnti a) (hp : ∀ n, 0 < a n)
    (hs : Summable a) (n : ℕ) : spectralSorted hs n=a n := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  have hnext (k : ℕ) (hk : spectralSelected hs k=Finset.range k) :
      spectralNext hs (spectralSelected hs k)=some k := by
    have hn : k ∉ spectralSelected hs k := by rw [hk]; simp
    cases he : spectralNext hs (spectralSelected hs k) with
    | none => exact (not_le_of_gt (hp k) (spectralNext_none hs he k hn)).elim
    | some i =>
      have hi := spectralNext_some hs he
      have hik : k ≤ i := by
        have hh := hi.1
        rw [hk] at hh
        simpa using hh
      have hie : i=k := by
        by_contra hh
        have hlt : k < i := by omega
        exact (not_lt_of_ge (hi.2.2 k hn)) (ha hlt)
      rw [hie]
  have hsel : ∀ k, spectralSelected hs k=Finset.range k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [spectralSelected,hnext k ih,Finset.range_add_one]
      simp only [ih]
      ext i
      simp
  exact spectralSorted_eq hs (hnext n (hsel n))

end
end chebyshev2.Continuum

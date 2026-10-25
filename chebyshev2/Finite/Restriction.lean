import chebyshev2.Finite.Realization

/-!
Article: chebyshev2, Theorem 2.1.
Restriction.
Use: `chebyshev2.Horizon.restrict_method_agree` feeds
`chebyshev2.Recurrence.jacobi_method_agree` (jacobi method agree).
Proof chain: `chebyshev2.recurrenceEquiv` — chebyshev2, Theorem 2.1; Bijection with all
admissible Jacobi matrices, including reducible matrices.
-/
namespace chebyshev2.Horizon
noncomputable section
open chebyshev1

/--
Constructs `restrictData` of type `JacobiData` by the displayed record fields. Data fields
specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Horizon.restrict_block` rewrites with this definition to establish exact
identity `(restrictData N J).block a n = J.block a n`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.
-/
def restrictData (N : ℕ) (J : JacobiData) : JacobiData where
  b i := if i < N then J.b i else 0
  aSq i := if i < N then J.aSq i else 0

/--
Exact identity `J.block a n = K.block a n`.

Use: `chebyshev2.Horizon.restrict_block` uses this identity to establish the identity
`(restrictData N J).block a n = J.block a n`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem block_congr {N : ℕ} {J K : JacobiData}
    (h : ∀ i < N, J.b i = K.b i ∧ J.aSq i = K.aSq i)
    (a n : ℕ) (hn : a+n ≤ N) : J.block a n = K.block a n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp only [JacobiData.block, (h a (by omega)).1]
  | more n ih0 ih1 =>
    simp only [JacobiData.block, (h (a+n+1) (by omega)).1,
      (h (a+n+1) (by omega)).2, ih0 (by omega), ih1 (by omega)]

/--
Exact identity `(restrictData N J).block a n = J.block a n`.

Use: `chebyshev2.Horizon.restrict_den` rewrites with this identity to establish exact
identity `(restrictData N J).den I n = J.den I n`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Use the identities/estimates `chebyshev2.Horizon.block_congr` with the arguments
shown in the proof.
-/
theorem restrict_block (N : ℕ) (J : JacobiData) (a n : ℕ) (hn : a+n ≤ N) :
    (restrictData N J).block a n = J.block a n :=
  block_congr (fun i hi => by simp [restrictData, hi]) a n hn

/--
Exact identity `(restrictData N J).den I n = J.den I n`.

Use: `chebyshev2.Horizon.restrict_method_agree` rewrites with this identity to establish
the precise assertion is `Agree N ((restrictData N J).method I) (J.method I)`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Use the identities/estimates `chebyshev2.Horizon.restrict_block` with the arguments
shown in the proof.
-/
theorem restrict_den (N : ℕ) (J : JacobiData) (I : SpectralInterval) (n : ℕ) (hn : n ≤ N) :
    (restrictData N J).den I n = J.den I n := by
  unfold JacobiData.den JacobiData.leading
  rw [restrict_block N J 0 n (by omega)]

/--
The precise assertion is `Agree N ((restrictData N J).method I) (J.method I)`.

Use: `chebyshev2.Recurrence.jacobi_method_agree` uses this assertion to establish the
precise assertion is `Horizon.Agree N ((R.jacobi I).data.method I) R.method`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: Use the identities/estimates `chebyshev2.Horizon.restrict_den` with the arguments
shown in the proof.
-/
theorem restrict_method_agree (N : ℕ) (J : JacobiData) (I : SpectralInterval) :
    Agree N ((restrictData N J).method I) (J.method I) := by
  intro i hi
  simp only [JacobiData.method,
    restrict_den N J I i (by omega), restrict_den N J I (i+1) (by omega),
    restrict_den N J I (i-1) (by omega)]
  simp [restrictData, hi]

end
end chebyshev2.Horizon

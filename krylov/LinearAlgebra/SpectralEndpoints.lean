import krylov.LinearAlgebra.SchurProduct
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Use: state actual continuation zero enclosures using the true extrema of the original computed spectrum.
Source: finite attained minimum and maximum of the actual original Hermitian eigenvalues.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The true smallest eigenvalue of the actual nonempty finite Hermitian matrix.
Use: The true smallest eigenvalue of the actual nonempty finite Hermitian matrix.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: Take the actual attained finite spectral infimum. -/
def spectralLower (T : Matrix ι ι ℝ) (hT : T.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hT.eigenvalues

/-- The true largest eigenvalue of the actual nonempty finite Hermitian matrix.
Use: The true largest eigenvalue of the actual nonempty finite Hermitian matrix.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: Take the actual attained finite spectral supremum. -/
def spectralUpper (T : Matrix ι ι ℝ) (hT : T.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hT.eigenvalues

/-- The actual smallest eigenvalue bounds every true spectral label from below.
Use: The actual smallest eigenvalue bounds every true spectral label from below.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: Use the genuine finite infimum bound. -/
theorem spectralLower_le (T : Matrix ι ι ℝ) (hT : T.IsHermitian) (i : ι) :
    spectralLower T hT≤hT.eigenvalues i := by
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The actual largest eigenvalue bounds every true spectral label from above.
Use: The actual largest eigenvalue bounds every true spectral label from above.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: Use the genuine finite supremum bound. -/
theorem le_spectralUpper (T : Matrix ι ι ℝ) (hT : T.IsHermitian) (i : ι) :
    hT.eigenvalues i≤spectralUpper T hT := by
  exact Finset.le_sup' _ (Finset.mem_univ i)

/-- The true smallest eigenvalue of the actual positive matrix is positive.
Use: The true smallest eigenvalue of the actual positive matrix is positive.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: The actual finite spectral infimum is attained at a genuine positive eigenvalue. -/
theorem spectralLower_pos (T : Matrix ι ι ℝ) (hT : T.PosDef) :
    0 < spectralLower T hT.1 := by
  -- Genuine attainment preserves strict endpoint inequalities at the actual finite spectral extrema.
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hT.1.eigenvalues
  rw [spectralLower,hi]
  exact hT.eigenvalues_pos i

/-- The true largest eigenvalue of the actual nonempty positive matrix is positive.
Use: The true largest eigenvalue of the actual nonempty positive matrix is positive.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: A genuine positive eigenvalue lies below the actual spectral maximum. -/
theorem spectralUpper_pos (T : Matrix ι ι ℝ) (hT : T.PosDef) :
    0 < spectralUpper T hT.1 := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hT.eigenvalues_pos i).trans_le (le_spectralUpper T hT.1 i)

/-- The actual closed extreme-eigenvalue interval lies strictly inside every true open spectral enclosure.
Use: The actual closed extreme-eigenvalue interval lies strictly inside every true open spectral enclosure.
Article: main_krylov, prop:phi(a), genuine smallest and largest finite Ritz values.
Proof: Both genuine finite extrema are attained at actual spectral labels, preserving their true strict endpoint margins. -/
theorem spectral_interval_inside (T : Matrix ι ι ℝ) (hT : T.IsHermitian)
    (a b : ℝ) (hlo : ∀ i,a<hT.eigenvalues i) (hhi : ∀ i,hT.eigenvalues i<b) :
    Set.Icc (spectralLower T hT) (spectralUpper T hT) ⊆ Set.Ioo a b := by
  -- Both true spectral extrema are attained at genuine labels before their strict endpoint margins are used.
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty hT.eigenvalues
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hT.eigenvalues
  intro x hx
  have hl : a<spectralLower T hT := by rw [spectralLower,hi];exact hlo i
  have hh : spectralUpper T hT<b := by rw [spectralUpper,hj];exact hhi j
  exact ⟨hl.trans_le hx.1,lt_of_le_of_lt hx.2 hh⟩
end
end krylov.LinearAlgebra

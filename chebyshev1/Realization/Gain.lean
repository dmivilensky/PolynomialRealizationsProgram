import chebyshev1.Realization.Basic
import chebyshev1.Chebyshev.Normalization
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: chebyshev1, Definition 1.2.
The supremum over both spectral parameters, exactly as in Definition 1.2.
Use: `chebyshev1.Realization.gain` feeds `chebyshev2.Horizon.gain_eq` (gain eq).
Proof chain: `chebyshev1.Stepsize.gain_lower_bound` — chebyshev1, Theorem 1.4; Sharp stepsize
drift lower bound and asymptotics.
-/
namespace chebyshev1.Realization
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Euclidean norm across insertion times at one spectral pair (Definition 1.2).

Use: `chebyshev1.Realization.gainValues` uses this definition in the displayed construction
of `gainValues`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.
-/
def kernelNorm (R : Realization ι) (N : ℕ) (lam nu : ℝ) : ℝ :=
  Real.sqrt (∑ s ∈ Finset.range N, (R.kernel N s lam nu) ^ 2)

/--
Defines `gainValues` of type `Set ℝ` by `{v | ∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu
I.L, v = R.kernelNorm N lam nu}`.

Use: `chebyshev1.Realization.gain` uses this definition in the displayed construction of
`gain`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.gain_eq_prefix`.
-/
def gainValues (R : Realization ι) (I : SpectralInterval) (N : ℕ) : Set ℝ :=
  {v | ∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu I.L,
    v = R.kernelNorm N lam nu}

/--
The supremum over both spectral parameters, exactly as in Definition 1.2.

Use: `chebyshev1.Realization.diagonal_hsSq_bound` uses this definition to establish the
stated quantitative bound `hsSq (R.linearResponse N (Matrix.diagonal eig) E) ≤ (R.gain I N) ^ 2
* ∑ s ∈ Finset.range N, hsSq (E s)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.
-/
def gain (R : Realization ι) (I : SpectralInterval) (N : ℕ) : ℝ :=
  sSup (R.gainValues I N)

end
end chebyshev1.Realization

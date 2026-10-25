import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Article: chebyshev1, Lemma E.8.
The continuant identity (3) used to extract the interior Fourier coefficients in E.8.
Use: `chebyshev1.Continuant.interior_identity` feeds
`chebyshev1.SineJacobi.blockFourier_interior_nonneg` (E.8: the coefficient of an interior block
is extracted at degree N+k).
Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities. The needed form is proved here.
-/
namespace chebyshev1.Continuant
noncomputable section
open scoped BigOperators
variable {R : Type*} [CommRing R] (d c : ℕ → R)

/--
Defines `continuant` by pattern matching with result type `ℕ → R`. The displayed branches
determine the recursive cases and their returned values.

Use: `chebyshev1.Continuant.block_left` rewrites with this definition to establish exact
identity `continuant d c a (n+2) = (d a)*continuant d c (a+1) (n+1) - (c (a+1))*continuant d c
(a+2) n`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.
-/
def continuant (a : ℕ) : ℕ → R
  | 0 => 1
  | 1 => d a
  | n+2 => d (a+n+1)*continuant a (n+1) - c (a+n+1)*continuant a n

/--
Expansion of a block along its first site.

Exact identity `continuant d c a (n+2) = (d a)*continuant d c (a+1) (n+1) - (c
(a+1))*continuant d c (a+2) n`.

Use: `chebyshev1.Continuant.terminal_block_left` uses this identity to establish exact
identity `continuant d c a (N-a) = (d a)*continuant d c (a+1) (N-(a+1)) - (c (a+1))*continuant
d c (a+2) (N-(a+2))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem block_left (a n : ℕ) :
    continuant d c a (n+2) = (d a)*continuant d c (a+1) (n+1) -
      (c (a+1))*continuant d c (a+2) n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp only [continuant]; ring
  | one => simp only [continuant]; ring
  | more n ih0 ih1 =>
    rw [show n+2+2 = (n+2)+2 by omega, continuant]
    rw [show n+2+1 = n+1+2 by omega, ih1, ih0]
    rw [continuant.eq_3 d c (a+1) (n+1), continuant.eq_3 d c (a+2) n]
    simp only [Nat.add_assoc]
    ring_nf

/--
Exact identity `continuant d c 0 (n+2) = (d (n+1))*continuant d c 0 (n+1) - (c
(n+1))*continuant d c 0 n`.

Use: `chebyshev1.Continuant.interior_identity` uses this identity to establish exact
identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a (N-a)
- (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem leading_add_two (n : ℕ) :
    continuant d c 0 (n+2) = (d (n+1))*continuant d c 0 (n+1) -
      (c (n+1))*continuant d c 0 n := by simp only [continuant, Nat.zero_add]

/--
Splitting a continuant across a coupling, with at least one site on each side.

Exact identity `continuant d c a (n+m+2) = continuant d c a (n+1)*continuant d c (a+n+1) (m+1)
- (c (a+n+1))*continuant d c a n*continuant d c (a+n+2) m`.

Use: `chebyshev1.Continuant.leading_split` uses this identity to establish the identity
`continuant d c 0 N = continuant d c 0 a*continuant d c a (N-a) - (c a)*continuant d c 0
(a-1)*continuant d c (a+1) (N-(a+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Induct on `m`; the recursive step uses the previous-stage assertion.
-/
theorem block_split (a n m : ℕ) :
    continuant d c a (n+m+2) = continuant d c a (n+1)*continuant d c (a+n+1) (m+1) -
      (c (a+n+1))*continuant d c a n*continuant d c (a+n+2) m := by
  -- Induct on `m`; the recursive step uses the previous-stage assertion.
  induction m using Nat.twoStepInduction with
  | zero => simp only [continuant]; ring
  | one => simp only [continuant, Nat.add_zero]; ring_nf
  | more m ih0 ih1 =>
    rw [show n+(m+2)+2 = (n+m+2)+2 by omega, continuant]
    rw [show n+m+2+1 = n+(m+1)+2 by omega, ih1, ih0]
    rw [continuant.eq_3 d c (a+n+1) (m+1), continuant.eq_3 d c (a+n+2) m]
    simp only [Nat.add_assoc]
    ring_nf

/--
Defines `couplingProduct` of type `R` by `∏ t ∈ Finset.range n, c (a+t)`.

Use: `chebyshev1.Continuant.interior_identity` rewrites with this definition to establish
exact identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a
(N-a) - (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.
-/
def couplingProduct (a n : ℕ) : R := ∏ t ∈ Finset.range n, c (a+t)

/--
Exact identity `couplingProduct c a (n+1) = couplingProduct c a n * c (a+n)`.

Use: `chebyshev1.Continuant.interior_identity` rewrites with this identity to establish
exact identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a
(N-a) - (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
@[simp] theorem couplingProduct_succ (a n : ℕ) :
    couplingProduct c a (n+1) = couplingProduct c a n * c (a+n) :=
  Finset.prod_range_succ _ _

/--
Exact identity `continuant d c a (N-a) = (d a)*continuant d c (a+1) (N-(a+1)) - (c
(a+1))*continuant d c (a+2) (N-(a+2))`.

Use: `chebyshev1.Continuant.interior_identity` uses this identity to establish exact
identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a (N-a)
- (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Use the identities/estimates `chebyshev1.Continuant.block_left` with the arguments
shown in the proof.
-/
theorem terminal_block_left {N a : ℕ} (ha : a+2 ≤ N) :
    continuant d c a (N-a) = (d a)*continuant d c (a+1) (N-(a+1)) -
      (c (a+1))*continuant d c (a+2) (N-(a+2)) := by
  have hh := block_left d c a (N-a-2)
  rw [show N-a-2+2 = N-a by omega, show N-a-2+1 = N-(a+1) by omega] at hh
  rw [show N-a-2 = N-(a+2) by omega] at hh
  exact hh

/--
Exact identity `continuant d c 0 N = continuant d c 0 a*continuant d c a (N-a) - (c
a)*continuant d c 0 (a-1)*continuant d c (a+1) (N-(a+1))`.

Use: `chebyshev1.Continuant.interior_identity` uses this identity to establish exact
identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a (N-a)
- (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Use the identities/estimates `chebyshev1.Continuant.block_split` with the arguments
shown in the proof.
-/
theorem leading_split {N a : ℕ} (ha : 0 < a) (haN : a < N) :
    continuant d c 0 N = continuant d c 0 a*continuant d c a (N-a) -
      (c a)*continuant d c 0 (a-1)*continuant d c (a+1) (N-(a+1)) := by
  -- Use the identities/estimates `chebyshev1.Continuant.block_split` with the arguments
  -- shown in the proof.
  have hh := block_split d c 0 (a-1) (N-a-1)
  simp only [Nat.zero_add] at hh
  rw [show a-1+(N-a-1)+2 = N by omega, show a-1+1 = a by omega,
    show a-1+2 = a+1 by omega, show N-a-1+1 = N-a by omega] at hh
  rw [show N-a-1 = N-(a+1) by omega] at hh
  exact hh

/--
The continuant identity (3) used to extract the interior Fourier coefficients in E.8.

Exact identity `continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a
(N-a) - (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1))`.

Use: `chebyshev1.SineJacobi.blockFourier_interior_nonneg` uses this identity to establish
the stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: chebyshev1, Corollary 5.3 via `chebyshev1.SineJacobi.G_exact`.

Source: Teschl, Jacobi Operators and Completely Integrable Nonlinear Lattices — continuant
recurrence and block determinant identities.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem interior_identity {N a : ℕ} (ha : 0 < a) (n : ℕ) (hn : a+n < N) :
    continuant d c 0 N*continuant d c a n = continuant d c 0 (a+n)*continuant d c a (N-a) -
      (couplingProduct c a (n+1))*continuant d c 0 (a-1)*continuant d c (a+n+1) (N-(a+n+1)) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero =>
    simpa [couplingProduct, continuant] using leading_split d c ha hn
  | one =>
    have hs := leading_split d c ha (show a < N by omega)
    have hl := terminal_block_left d c (show a+2 ≤ N by omega)
    have hp := leading_add_two d c (a-1)
    rw [show a-1+2 = a+1 by omega, show a-1+1 = a by omega] at hp
    simp only [continuant, couplingProduct, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, Nat.add_zero]
    rw [hp]
    linear_combination (d a)*hs + (c a)*continuant d c 0 (a-1)*hl
  | more n ih0 ih1 =>
    have h0 := ih0 (show a+n < N by omega)
    have h1 := ih1 (show a+(n+1) < N by omega)
    have hl := terminal_block_left d c (show (a+n+1)+2 ≤ N by omega)
    have hp := leading_add_two d c (a+n)
    simp only [Nat.add_assoc] at h1 hl hp ⊢
    rw [hp, continuant.eq_3 d c a n]
    rw [couplingProduct_succ, couplingProduct_succ]
    rw [couplingProduct_succ] at h1
    simp only [Nat.add_assoc] at h0 h1 ⊢
    linear_combination (d (a+(n+1)))*h1 - (c (a+(n+1)))*h0 +
      (couplingProduct c a (n+1))*(c (a+(n+1)))*continuant d c 0 (a-1)*hl

end
end chebyshev1.Continuant

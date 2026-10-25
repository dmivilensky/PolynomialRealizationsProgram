import chebyshev1.Jacobi.Basic

/-!
Article: chebyshev1, Lemma E.5.
The continuant identity (3) used to extract the interior Fourier coefficients in E.8.
Use: `chebyshev1.JacobiData.interior_identity` feeds
`chebyshev1.JacobiData.spectral_endpoint_product` (E.5's product identity follows from two
diagonal cofactors and a continuant identity).
Proof chain: `chebyshev1.SineJacobi.spectral_weight` — chebyshev1, Theorem E.1; Sine-lattice
couplings, spectrum, expansion and symmetry.
-/
namespace chebyshev1.JacobiData
noncomputable section
open Polynomial
open scoped BigOperators
variable (J : JacobiData)

/--
Expansion of a block along its first site.

Exact identity `J.block a (n+2) = (X-C (J.b a))*J.block (a+1) (n+1) - C (J.aSq (a+1))*J.block
(a+2) n`.

Use: `chebyshev1.JacobiData.terminal_block_left` uses this identity to establish exact
identity `J.block a (N-a) = (X-C (J.b a))*J.block (a+1) (N-(a+1)) - C (J.aSq (a+1))*J.block
(a+2) (N-(a+2))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.block_pair_unique`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem block_left (a n : ℕ) :
    J.block a (n+2) = (X-C (J.b a))*J.block (a+1) (n+1) -
      C (J.aSq (a+1))*J.block (a+2) n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp only [block]; ring
  | one => simp only [block]; ring
  | more n ih0 ih1 =>
    rw [show n+2+2 = (n+2)+2 by omega, block]
    rw [show n+2+1 = n+1+2 by omega, ih1, ih0]
    rw [block.eq_3 J (a+1) (n+1), block.eq_3 J (a+2) n]
    simp only [Nat.add_assoc]
    ring_nf

/--
Exact identity `J.leading (n+2) = (X-C (J.b (n+1)))*J.leading (n+1) - C (J.aSq (n+1))*J.leading
n`.

Use: `chebyshev1.JacobiData.interior_identity` uses this identity to establish exact
identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C (J.couplingProduct a
(n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem leading_add_two (n : ℕ) :
    J.leading (n+2) = (X-C (J.b (n+1)))*J.leading (n+1) -
      C (J.aSq (n+1))*J.leading n := by simp only [leading, block, Nat.zero_add]

/--
Splitting a continuant across a coupling, with at least one site on each side.

Exact identity `J.block a (n+m+2) = J.block a (n+1)*J.block (a+n+1) (m+1) - C (J.aSq
(a+n+1))*J.block a n*J.block (a+n+2) m`.

Use: `chebyshev1.JacobiData.leading_split` uses this identity to establish the identity
`J.leading N = J.leading a*J.block a (N-a) - C (J.aSq a)*J.leading (a-1)*J.block (a+1)
(N-(a+1))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: Induct on `m`; the recursive step uses the previous-stage assertion.
-/
theorem block_split (a n m : ℕ) :
    J.block a (n+m+2) = J.block a (n+1)*J.block (a+n+1) (m+1) -
      C (J.aSq (a+n+1))*J.block a n*J.block (a+n+2) m := by
  -- Induct on `m`; the recursive step uses the previous-stage assertion.
  induction m using Nat.twoStepInduction with
  | zero => simp only [block]; ring
  | one => simp only [block, Nat.add_zero]; ring_nf
  | more m ih0 ih1 =>
    rw [show n+(m+2)+2 = (n+m+2)+2 by omega, block]
    rw [show n+m+2+1 = n+(m+1)+2 by omega, ih1, ih0]
    rw [block.eq_3 J (a+n+1) (m+1), block.eq_3 J (a+n+2) m]
    simp only [Nat.add_assoc]
    ring_nf

/--
Defines `couplingProduct` of type `ℝ` by `∏ t ∈ Finset.range n, J.aSq (a+t)`.

Use: `chebyshev1.JacobiData.interior_identity` rewrites with this definition to establish
exact identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C
(J.couplingProduct a (n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.spectral_weight`.
-/
def couplingProduct (a n : ℕ) : ℝ := ∏ t ∈ Finset.range n, J.aSq (a+t)

/--
Exact identity `J.couplingProduct a (n+1) = J.couplingProduct a n * J.aSq (a+n)`.

Use: `chebyshev1.JacobiData.interior_identity` rewrites with this identity to establish
exact identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C
(J.couplingProduct a (n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
@[simp] theorem couplingProduct_succ (a n : ℕ) :
    J.couplingProduct a (n+1) = J.couplingProduct a n * J.aSq (a+n) :=
  Finset.prod_range_succ _ _

/--
Exact identity `J.block a (N-a) = (X-C (J.b a))*J.block (a+1) (N-(a+1)) - C (J.aSq
(a+1))*J.block (a+2) (N-(a+2))`.

Use: `chebyshev1.JacobiData.interior_identity` uses this identity to establish exact
identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C (J.couplingProduct a
(n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.block_left` with the arguments
shown in the proof.
-/
theorem terminal_block_left {N a : ℕ} (ha : a+2 ≤ N) :
    J.block a (N-a) = (X-C (J.b a))*J.block (a+1) (N-(a+1)) -
      C (J.aSq (a+1))*J.block (a+2) (N-(a+2)) := by
  have hh := J.block_left a (N-a-2)
  rw [show N-a-2+2 = N-a by omega, show N-a-2+1 = N-(a+1) by omega] at hh
  rw [show N-a-2 = N-(a+2) by omega] at hh
  exact hh

/--
Exact identity `J.leading N = J.leading a*J.block a (N-a) - C (J.aSq a)*J.leading (a-1)*J.block
(a+1) (N-(a+1))`.

Use: `chebyshev1.JacobiData.interior_identity` uses this identity to establish exact
identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C (J.couplingProduct a
(n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.block_split` with the arguments
shown in the proof.
-/
theorem leading_split {N a : ℕ} (ha : 0 < a) (haN : a < N) :
    J.leading N = J.leading a*J.block a (N-a) -
      C (J.aSq a)*J.leading (a-1)*J.block (a+1) (N-(a+1)) := by
  -- Use the identities/estimates `chebyshev1.JacobiData.block_split` with the arguments
  -- shown in the proof.
  have hh := J.block_split 0 (a-1) (N-a-1)
  simp only [Nat.zero_add] at hh
  rw [show a-1+(N-a-1)+2 = N by omega, show a-1+1 = a by omega,
    show a-1+2 = a+1 by omega, show N-a-1+1 = N-a by omega] at hh
  rw [show N-a-1 = N-(a+1) by omega] at hh
  exact hh

/--
The continuant identity (3) used to extract the interior Fourier coefficients in E.8.

Exact identity `J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) - C
(J.couplingProduct a (n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1))`.

Use: `chebyshev1.JacobiData.spectral_endpoint_product` uses this identity to establish
exact identity `B.weight 0 j * B.weight (Fin.last n) j * ((J.leading (n+1)).derivative.eval
(B.eigenvalues j))^2 = J.couplingProduct 1 n`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem interior_identity {N a : ℕ} (ha : 0 < a) (n : ℕ) (hn : a+n < N) :
    J.leading N*J.block a n = J.leading (a+n)*J.block a (N-a) -
      C (J.couplingProduct a (n+1))*J.leading (a-1)*J.block (a+n+1) (N-(a+n+1)) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero =>
    simpa [couplingProduct, block] using J.leading_split ha hn
  | one =>
    have hs := J.leading_split ha (show a < N by omega)
    have hl := J.terminal_block_left (show a+2 ≤ N by omega)
    have hp := J.leading_add_two (a-1)
    rw [show a-1+2 = a+1 by omega, show a-1+1 = a by omega] at hp
    simp only [block, couplingProduct, Finset.prod_range_succ, Finset.prod_range_zero,
      one_mul, Nat.add_zero, C_mul]
    rw [hp]
    linear_combination (X-C (J.b a))*hs + C (J.aSq a)*J.leading (a-1)*hl
  | more n ih0 ih1 =>
    have h0 := ih0 (show a+n < N by omega)
    have h1 := ih1 (show a+(n+1) < N by omega)
    have hl := J.terminal_block_left (show (a+n+1)+2 ≤ N by omega)
    have hp := J.leading_add_two (a+n)
    simp only [Nat.add_assoc] at h1 hl hp ⊢
    rw [hp, block.eq_3 J a n]
    rw [couplingProduct_succ, couplingProduct_succ, C_mul, C_mul]
    rw [couplingProduct_succ, C_mul] at h1
    simp only [Nat.add_assoc] at h0 h1 ⊢
    linear_combination (X-C (J.b (a+(n+1))))*h1 - C (J.aSq (a+(n+1)))*h0 +
      C (J.couplingProduct a (n+1))*C (J.aSq (a+(n+1)))*J.leading (a-1)*hl

end
end chebyshev1.JacobiData

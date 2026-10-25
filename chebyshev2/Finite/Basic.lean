import chebyshev1.Jacobi.Admissibility
import chebyshev1.Jacobi.Prefix
import chebyshev1.Jacobi.InverseUniqueness
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
Article: chebyshev2, Theorem 1.1.
The article's full fiber Y_N, with nonnegative couplings.
Use: `chebyshev2.ExactRecurrence` feeds `chebyshev2.SineJacobi.symmetric_gain_exact`
(symmetric gain exact).
Proof chain: `chebyshev2.DualCertificate.uniform_sine_of_finite_lower` — chebyshev2, Theorem
1.2; Analytic gain reduction and uniform sine comparison.
-/
namespace chebyshev2
noncomputable section
open Polynomial Polynomial.Chebyshev

/--
A finite Jacobi chain. Incoming coupling zero and the unused tails are fixed, so the
representation has exactly N diagonal and N-1 coupling parameters.

Use: `chebyshev2.Jacobi.Irreducible` uses this record of data and proof obligations in the
displayed construction of `Irreducible`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
@[ext] structure Jacobi (N : ℕ) where
  /-- Jacobi coefficients shared with chebyshev1. -/
  data : chebyshev1.JacobiData
  /-- Nonnegative squared couplings, allowing reducible matrices when a coupling vanishes. -/
  coupling_nonneg : ∀ i, 0 ≤ data.aSq i
  /-- The unused coupling before the first row is zero. -/
  coupling_zero : data.aSq 0 = 0
  /-- Zero extension of the diagonal beyond the N-dimensional block. -/
  diagonal_tail : ∀ i, N ≤ i → data.b i = 0
  /-- Zero extension of the squared couplings beyond the N-dimensional block. -/
  coupling_tail : ∀ i, N ≤ i → data.aSq i = 0

/--
The monic Chebyshev polynomial, including the empty chain.

Use: `chebyshev2.Jacobi.Terminal` uses this definition in the displayed construction of
`Terminal`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace`.
-/
def fiberPolynomial (N : ℕ) : ℝ[X] := chebyshev1.Prefix.jacobiData.leading N

/--
Exact identity `fiberPolynomial (n+1) = C ((1/2 : ℝ)^n) * T ℝ (n+1)`.

Use: `chebyshev2.Jacobi.spectrum_eq_nodes` rewrites with this identity to establish exact
identity `spectrum ℝ J.matrix = Set.range (fun k : Fin N => Real.cos
((2*(k:ℝ)+1)*Real.pi/(2*(N:ℝ))))`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace`.

Proof: Use the identities/estimates `chebyshev1.Prefix.jacobi_leading` with the arguments
shown in the proof.
-/
theorem fiberPolynomial_succ (n : ℕ) :
    fiberPolynomial (n+1) = C ((1/2 : ℝ)^n) * T ℝ (n+1) :=
  chebyshev1.Prefix.jacobi_leading n

/--
Exact identity `fiberPolynomial N = C (2/(2:ℝ)^N)*T ℝ N`.

Use: `chebyshev2.Continuum.chebyshev_node_product` rewrites with this identity to establish
exact identity `(∏ j : Fin N, (z - chebyshev1.SineJacobi.node N j)) = 2 / (2 : ℝ)^N * (T ℝ
N).eval z`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem fiberPolynomial_eq (N : ℕ) (hN : 0 < N) :
    fiberPolynomial N = C (2/(2:ℝ)^N)*T ℝ N := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [fiberPolynomial_succ]
  have hc : (1/2:ℝ)^n = 2/(2:ℝ)^(n+1) := by
    rw [div_pow, one_pow, pow_succ]
    field_simp
  rw [hc]
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]

/--
The article's full fiber Y_N, with nonnegative couplings.

Use: `chebyshev2.Jacobi.admissible` uses this definition to establish the precise assertion
is `J.data.Admissible I N`.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
def Jacobi.Terminal {N : ℕ} (J : Jacobi N) : Prop :=
  J.data.leading N = fiberPolynomial N

/--
Defines `Fiber` of type `(N : ℕ)` by `{J : Jacobi N // J.Terminal}`.

Use: `chebyshev2.Calibration.Data.greenConstant_ge_referenceBase` uses this definition to
establish the stated quantitative bound `C.referenceBase ≤ greenConstant`.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.
-/
abbrev Fiber (N : ℕ) := {J : Jacobi N // J.Terminal}

namespace Jacobi
variable {N : ℕ} (J : Jacobi N)

/--
Defines `matrix` of type `` by `J.data.matrix 0 N`.

Use: `chebyshev2.Jacobi.green` uses this definition in the displayed construction of
`green`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.cholesky_factor`.
-/
def matrix := J.data.matrix 0 N
/--
Defines `green` of type `` by `(1-J.matrix)⁻¹`.

Use: `chebyshev2.Jacobi.centered_green_diagonal` uses this definition to establish exact
identity `J.green i i = 1+J.incomingFlow i+J.edgeFlow i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def green := (1-J.matrix)⁻¹
/--
Defines `energy` of type `ℝ` by `∑ i : Fin N, (J.green i i)^2`.

Use: `chebyshev2.Jacobi.endpoint_norm` rewrites with this definition to establish exact
identity `(J.data.realization I).kernelNorm N I.mu I.mu = 2*I.epsilon N/I.delta*Real.sqrt
J.energy`.

Article: chebyshev2, Theorem 2.5 via `chebyshev2.SineJacobi.gain_exact`.
-/
def energy : ℝ := ∑ i : Fin N, (J.green i i)^2
/--
Defines `Irreducible` of type `Prop` by `∀ i, 0 < i → i < N → 0 < J.data.aSq i`.

Use: `chebyshev2.Jacobi.Centered` uses this definition in the displayed construction of
`Centered`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_irreducible_iff`.
-/
def Irreducible : Prop := ∀ i, 0 < i → i < N → 0 < J.data.aSq i
/--
Defines `Centered` of type `Prop` by `J.Irreducible ∧ ∀ i < N, J.data.b i = 0`.

Use: `chebyshev2.CenteredFiber` uses this definition in the displayed construction of
`CenteredFiber`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.
-/
def Centered : Prop := J.Irreducible ∧ ∀ i < N, J.data.b i = 0

/--
The precise assertion is `J.matrix.IsHermitian`.

Use: `chebyshev2.Continuum.chebyshev_node_product` uses this assertion to establish exact
identity `(∏ j : Fin N, (z - chebyshev1.SineJacobi.node N j)) = 2 / (2 : ℝ)^N * (T ℝ
N).eval z`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_spectrum`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.matrix_isHermitian` with the
arguments shown in the proof.
-/
theorem matrix_isHermitian : J.matrix.IsHermitian := J.data.matrix_isHermitian 0 N

/--
Exact identity `J.matrix.charpoly = fiberPolynomial N`.

Use: `chebyshev2.Jacobi.spectrum_eq_nodes` rewrites with this identity to establish exact
identity `spectrum ℝ J.matrix = Set.range (fun k : Fin N => Real.cos
((2*(k:ℝ)+1)*Real.pi/(2*(N:ℝ))))`.

Article: chebyshev2, Theorem A.1 via `chebyshev2.Jacobi.green_trace_square`.

Proof: Use the identities/estimates `chebyshev1.JacobiData.block_eq_charpoly` with the
arguments shown in the proof.
-/
theorem charpoly_eq (h : J.Terminal) : J.matrix.charpoly = fiberPolynomial N := by
  rw [matrix, ← J.data.block_eq_charpoly J.coupling_nonneg]
  exact h

/--
Exact identity `spectrum ℝ J.matrix = Set.range (fun k : Fin N => Real.cos
((2*(k:ℝ)+1)*Real.pi/(2*(N:ℝ))))`.

Use: `chebyshev2.Jacobi.spectrum_subset` rewrites with this identity to establish the
precise assertion is `spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.admissible`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.charpoly_eq`,
`chebyshev2.fiberPolynomial_succ` with the arguments shown in the proof.
-/
theorem spectrum_eq_nodes (hN : 0 < N) (h : J.Terminal) :
    spectrum ℝ J.matrix =
      Set.range (fun k : Fin N => Real.cos ((2*(k:ℝ)+1)*Real.pi/(2*(N:ℝ)))) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.charpoly_eq`,
  -- `chebyshev2.fiberPolynomial_succ` with the arguments shown in the proof.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, J.charpoly_eq h, fiberPolynomial_succ]
  simp only [IsRoot, eval_mul, eval_C, mul_eq_zero,
    pow_ne_zero n (by norm_num : (1/2:ℝ) ≠ 0), false_or]
  rw [← IsRoot, ← mem_roots (T_ne_zero ℝ (n+1))]
  rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega, roots_T_real]
  simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range, Set.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k,hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k.val, k.isLt, rfl⟩

/--
The precise assertion is `spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1`.

Use: `chebyshev2.Jacobi.admissible` uses this assertion to establish the precise assertion
is `J.data.Admissible I N`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.admissible`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.spectrum_eq_nodes` with the
arguments shown in the proof.
-/
theorem spectrum_subset (hN : 0 < N) (h : J.Terminal) :
    spectrum ℝ J.matrix ⊆ Set.Icc (-1) 1 := by
  rw [J.spectrum_eq_nodes hN h]
  rintro _ ⟨k,rfl⟩
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/--
Positivity of all principal determinants at z_0 (Theorem 2.1).

The precise assertion is `J.data.Admissible I N`.

Use: `chebyshev2.DualCertificate.uniform_sine_of_finite_lower` uses this assertion to
establish the bound stated in that declaration.

Article: chebyshev2, Theorem 2.1.

Proof: Use the identities/estimates `chebyshev1.JacobiData.admissible_of_spectrum`,
`chebyshev2.Jacobi.spectrum_subset` with the arguments shown in the proof.
-/
theorem admissible (I : chebyshev1.SpectralInterval) (hN : 0 < N) (h : J.Terminal) :
    J.data.Admissible I N :=
  J.data.admissible_of_spectrum I N J.coupling_nonneg (J.spectrum_subset hN h)

end Jacobi

/--
Definition 1, represented by the existing chebyshev1 recurrence. Outside the finite horizon
the coefficients are fixed to (alpha,beta,gamma)=(1,0,1). chebyshev1 stores the signed memory
coefficient b=-beta.

Use: `chebyshev2.ExactRecurrence` uses this record of data and proof obligations in the
displayed construction of `ExactRecurrence`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.
-/
@[ext] structure Recurrence (N : ℕ) where
  /-- Two-term recurrence data shared with chebyshev1. -/
  method : chebyshev1.TwoTerm
  /-- The two memory coefficients sum to one at every step. -/
  normalized : ∀ i, method.a i + method.b i = 1
  /-- Every stepsize is strictly positive. -/
  gamma_pos : ∀ i, 0 < method.gamma i
  /-- The preceding-error coefficient has the admissible nonpositive sign. -/
  memory_nonpos : ∀ i, method.b i ≤ 0
  /-- The initial step has no preceding-error memory term. -/
  memory_zero : method.b 0 = 0
  /-- Canonical extension of the current-error coefficient beyond the finite recurrence. -/
  alpha_tail : ∀ i, N ≤ i → method.a i = 1
  /-- Memory vanishes beyond the finite recurrence. -/
  memory_tail : ∀ i, N ≤ i → method.b i = 0
  /-- Canonical unit stepsize beyond the finite recurrence. -/
  gamma_tail : ∀ i, N ≤ i → method.gamma i = 1

namespace Recurrence
variable {N : ℕ} (R : Recurrence N)
/--
Defines `alpha` of type `(i : ℕ)` by `R.method.a i`.

Use: `chebyshev2.Recurrence.alpha_eq` uses this definition to establish the identity
`R.alpha i = 1 + R.beta i`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.
-/
def alpha (i : ℕ) := R.method.a i
/--
Defines `beta` of type `(i : ℕ)` by `-R.method.b i`.

Use: `chebyshev2.Recurrence.alpha_eq` uses this definition to establish the identity
`R.alpha i = 1 + R.beta i`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_irreducible_iff`.
-/
def beta (i : ℕ) := -R.method.b i
/--
Defines `gamma` of type `(i : ℕ)` by `R.method.gamma i`.

Use: `chebyshev2.Jacobi.jacobi_recurrence` rewrites with this definition to establish exact
identity `(J.recurrence I h).jacobi I = J`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.
-/
def gamma (i : ℕ) := R.method.gamma i
/--
Defines `Terminal` of type `Prop` by `R.method.realization.residualPolynomial N = I.residual
N`.

Use: `chebyshev2.Jacobi.admissible` uses this definition to establish the precise assertion
is `J.data.Admissible I N`.

Article: chebyshev2, Theorem 1.2 via `chebyshev2.Optimal.greenConstant_le_sine`.
-/
def Terminal (I : chebyshev1.SpectralInterval) : Prop :=
  R.method.realization.residualPolynomial N = I.residual N
/--
Defines `Irreducible` of type `Prop` by `∀ i, 0 < i → i < N → 0 < R.beta i`.

Use: `chebyshev2.Jacobi.Centered` uses this definition in the displayed construction of
`Centered`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_irreducible_iff`.
-/
def Irreducible : Prop := ∀ i, 0 < i → i < N → 0 < R.beta i
/--
Defines `Centered` of type `Prop` by `R.Irreducible ∧ ∀ i < N, R.alpha i = (I.L+I.mu)/2 *
R.gamma i`.

Use: `chebyshev2.CenteredFiber` uses this definition in the displayed construction of
`CenteredFiber`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.Jacobi.recurrence_centered_iff`.
-/
def Centered (I : chebyshev1.SpectralInterval) : Prop :=
  R.Irreducible ∧ ∀ i < N, R.alpha i = (I.L+I.mu)/2 * R.gamma i
/--
Exact identity `R.alpha i = 1 + R.beta i`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 1.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem alpha_eq (i : ℕ) : R.alpha i = 1 + R.beta i := by
  dsimp [alpha, beta]; linarith [R.normalized i]
/--
The stated quantitative bound `0 ≤ R.beta i`.

Use: `chebyshev2.Recurrence.inverseData_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ (R.inverseData I).aSq i`.

Article: chebyshev2, Theorem 2.1 via `chebyshev2.recurrenceEquiv`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem beta_nonneg (i : ℕ) : 0 ≤ R.beta i := neg_nonneg.mpr (R.memory_nonpos i)
end Recurrence

/--
Defines `ExactRecurrence` of type `(I : chebyshev1.SpectralInterval) (N : ℕ)` by `{R :
Recurrence N // R.Terminal I}`.

Use: `chebyshev2.Optimal.gainValues` uses this definition in the displayed construction of
`gainValues`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 1.2 via
`chebyshev2.DualCertificate.uniform_sine_of_finite_lower`.
-/
abbrev ExactRecurrence (I : chebyshev1.SpectralInterval) (N : ℕ) :=
  {R : Recurrence N // R.Terminal I}

end
end chebyshev2

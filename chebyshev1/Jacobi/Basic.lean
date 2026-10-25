import chebyshev1.TwoTerm.Quadratic

/-!
Article: chebyshev1, Theorem 4.2.
A block polynomial expressed in the physical spectral variable lambda.
Use: `chebyshev1.JacobiData.residual_eval` feeds `chebyshev1.JacobiData.scalar_exact` (The
scalar form of Theorem 4.1, including the initial prefix).
Proof chain: `chebyshev1.JacobiData.kernel_eq` — chebyshev1, Theorem 4.2; Block determinants,
first-variation kernel and gain.
-/
namespace chebyshev1
noncomputable section
open Polynomial
open scoped Polynomial

/--
Jacobi recurrence data. `aSq s` is the squared coupling between sites s-1 and s.

Use: `chebyshev1.JacobiData.den_one` uses this record of data and proof obligations to
establish exact identity `J.den I 1 = I.eta - J.b 0`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
structure JacobiData where
  /-- Diagonal Jacobi coefficients. -/
  b : ℕ → ℝ
  /-- Coefficients representing squared off-diagonal couplings. Determinant recursions use these values algebraically; admissibility imposes nonnegativity. -/
  aSq : ℕ → ℝ

namespace JacobiData

/--
Monic continuants of a contiguous block, with its start and length explicit.

Use: `chebyshev1.JacobiData.den_add_two` rewrites with this definition to establish exact
identity `J.den I (n + 2) = (I.eta - J.b (n + 1)) * J.den I (n + 1) - J.aSq (n + 1) * J.den I
n`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.
-/
def block (J : JacobiData) (a : ℕ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X - C (J.b a)
  | n + 2 => (X - C (J.b (a + n + 1))) * J.block a (n + 1) -
      C (J.aSq (a + n + 1)) * J.block a n

/--
Defines `leading` of type `ℝ[X]` by `J.block 0 n`.

Use: `chebyshev1.JacobiData.residual_eval` uses this definition to establish the identity
`(J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.leading_endpoint_max`.
-/
def leading (J : JacobiData) (n : ℕ) : ℝ[X] := J.block 0 n
/--
Defines `den` of type `ℝ` by `(J.leading n).eval I.eta`.

Use: `chebyshev1.JacobiData.Admissible` uses this definition in the displayed construction
of `Admissible`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.
-/
def den (J : JacobiData) (I : SpectralInterval) (n : ℕ) : ℝ := (J.leading n).eval I.eta
/--
Defines `Admissible` of type `Prop` by `∀ n ≤ N, 0 < J.den I n`.

Use: `chebyshev1.JacobiData.G_eq_chebyshev_coeff` uses this definition to establish exact
identity `J.G N k = 2 / (2 : ℝ)^k * (taylor 1 (T ℝ N)).coeff k`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def Admissible (J : JacobiData) (I : SpectralInterval) (N : ℕ) : Prop :=
  ∀ n ≤ N, 0 < J.den I n

/--
Defines `residual` of type `ℝ[X]` by `C (J.den I n)⁻¹ * (J.leading n).comp (C I.eta - C (2 /
I.delta) * X)`.

Use: `chebyshev1.JacobiData.residual_eval` rewrites with this definition to establish exact
identity `(J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_finiteDrift_le`.
-/
def residual (J : JacobiData) (I : SpectralInterval) (n : ℕ) : ℝ[X] :=
  C (J.den I n)⁻¹ * (J.leading n).comp (C I.eta - C (2 / I.delta) * X)

/--
A block polynomial expressed in the physical spectral variable lambda.

Use: `chebyshev1.JacobiData.spectralBlock_eval` rewrites with this definition to establish
exact identity `(J.spectralBlock I a n).eval lam = (J.block a n).eval (I.z lam)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def spectralBlock (J : JacobiData) (I : SpectralInterval) (a n : ℕ) : ℝ[X] :=
  (J.block a n).comp (C I.eta - C (2 / I.delta) * X)

/--
Exact identity `(J.spectralBlock I a n).eval lam = (J.block a n).eval (I.z lam)`.

Use: `chebyshev1.JacobiData.linearResponse_blocks` rewrites with this identity to establish
exact identity `(J.realization I).linearResponse N H E = -(2 / (I.delta * J.den I N)) • ∑ s ∈
Finset.range N, aeval H (J.spectralBlock I (s + 1) (N - (s + 1))) * E s * aeval H
(J.spectralBlock I 0 s)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_eq` with the arguments
shown in the proof.
-/
theorem spectralBlock_eval (J : JacobiData) (I : SpectralInterval) (a n : ℕ) (lam : ℝ) :
    (J.spectralBlock I a n).eval lam = (J.block a n).eval (I.z lam) := by simp [spectralBlock, I.z_eq]

/--
Constructs `method` of type `TwoTerm` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `chebyshev1.JacobiData.fixed_point` uses this definition to establish the identity
`(J.method I).a (n + 1) + (J.method I).b (n + 1) = 1`.

Article: chebyshev1, Corollary 5.4 via `chebyshev1.Nonlinear.lipschitzHessian_error_le`.
-/
def method (J : JacobiData) (I : SpectralInterval) : TwoTerm where
  a := fun t => J.den I t / J.den I (t + 1) * (I.eta - J.b t)
  b := fun t => -(J.aSq t * J.den I (t - 1) / J.den I (t + 1))
  gamma := fun t => (2 / I.delta) * J.den I t / J.den I (t + 1)

/--
Defines `realization` of type `Realization (Fin 2)` by `(J.method I).realization`.

Use: `chebyshev1.JacobiData.driftOrder` uses this definition in the displayed construction
of `driftOrder`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def realization (J : JacobiData) (I : SpectralInterval) : Realization (Fin 2) :=
  (J.method I).realization

/--
Exact identity `J.leading 0 = 1`.

Use: `chebyshev1.JacobiData.spectral_endpoint_product` rewrites with this identity to
establish exact identity `B.weight 0 j * B.weight (Fin.last n) j * ((J.leading
(n+1)).derivative.eval (B.eigenvalues j))^2 = J.couplingProduct 1 n`.

Article: chebyshev1, Lemma E.5 via `chebyshev1.JacobiData.spectral_endpoint_product`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem leading_zero (J : JacobiData) : J.leading 0 = 1 := rfl
/--
Exact identity `J.leading 1 = X - C (J.b 0)`.

Use: `chebyshev1.JacobiData.leading_aeval_site` rewrites with this identity to establish
exact identity `aeval (J.matrix 0 N) (J.leading s) *ᵥ site N 0 = J.linkProduct s • site N s`.

Article: chebyshev1, Lemma E.2 via `chebyshev1.SineJacobi.leading_orthogonality`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem leading_one (J : JacobiData) : J.leading 1 = X - C (J.b 0) := rfl
/--
Exact identity `J.den I 0 = 1`.

Use: `chebyshev1.JacobiData.prefix_column` rewrites with this identity to establish the
precise assertion is `let M`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem den_zero (J : JacobiData) (I : SpectralInterval) : J.den I 0 = 1 := by simp [den]
/--
Exact identity `J.den I 1 = I.eta - J.b 0`.

Use: `chebyshev1.JacobiData.prefix_column` rewrites with this identity to establish the
precise assertion is `let M`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem den_one (J : JacobiData) (I : SpectralInterval) : J.den I 1 = I.eta - J.b 0 := by simp [den]

/--
Exact identity `J.den I (n + 2) = (I.eta - J.b (n + 1)) * J.den I (n + 1) - J.aSq (n + 1) *
J.den I n`.

Use: `chebyshev1.JacobiData.fixed_point` uses this identity to establish the identity
`(J.method I).a (n + 1) + (J.method I).b (n + 1) = 1`.

Article: chebyshev1, Theorem 4.1 via `chebyshev1.JacobiData.fixed_point`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem den_add_two (J : JacobiData) (I : SpectralInterval) (n : ℕ) :
    J.den I (n + 2) = (I.eta - J.b (n + 1)) * J.den I (n + 1) -
      J.aSq (n + 1) * J.den I n := by simp [den, leading, block]

/--
Exact identity `(J.method I).a (n + 1) + (J.method I).b (n + 1) = 1`.

Use: `chebyshev2.Jacobi.recurrence` uses this identity in the displayed construction of
`recurrence`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev1, Theorem 4.1.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem fixed_point (J : JacobiData) (I : SpectralInterval) (n : ℕ)
    (hne : J.den I (n + 2) ≠ 0) :
    (J.method I).a (n + 1) + (J.method I).b (n + 1) = 1 := by
  dsimp [method]
  field_simp [hne]
  nlinarith [J.den_add_two I n]

/--
Exact identity `(J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n`.

Use: `chebyshev1.JacobiData.kernel_eq` uses this identity to establish the identity
`(J.realization I).kernel N s lam nu = -(2 / (I.delta * J.den I N)) * (J.block (s + 1) (N - (s
+ 1))).eval (I.z lam) * (J.leading s).eval (I.z nu)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.kernel_abs_le_endpoint`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_eq` with the arguments
shown in the proof.
-/
theorem residual_eval (J : JacobiData) (I : SpectralInterval) (n : ℕ) (lam : ℝ) :
    (J.residual I n).eval lam = (J.leading n).eval (I.z lam) / J.den I n := by simp [residual, I.z_eq, div_eq_mul_inv, mul_comm]

end JacobiData
end
end chebyshev1

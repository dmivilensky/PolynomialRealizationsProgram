import chebyshev1.Realization.Basic
import chebyshev1.Algebra.FirstVariation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
Article: chebyshev1, Lemma 1.1.
Lemma 1.1: the insertion sum is the actual derivative at zero drift.
Use: `chebyshev1.Realization.hasDerivAt_operatorTransfer` feeds
`chebyshev1.Realization.kernel_sum_derivative` (The sum of all insertion kernels is the
derivative under a static spectral shift).
Proof chain: `chebyshev1.Realization.static_shift_lower_bounds_general` — chebyshev1, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace chebyshev1.Realization

open scoped BigOperators Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/--
The term linear in all Hessian perturbations, with the paper's sign convention.

Use: `chebyshev1.Realization.operatorTransfer_decomposition` uses this definition to
establish exact identity `R.operatorTransfer n (fun s => H + E s) = R.operatorTransfer n (fun _
=> H) + R.linearResponse n H E + R.driftRemainder n H E`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.
-/
def linearResponse (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) : Matrix d d ℝ :=
  R.contract (firstVariation (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (E s)) n)

/--
Terms containing at least two insertions.

Use: `chebyshev1.Realization.operatorTransfer_decomposition` uses this definition to
establish exact identity `R.operatorTransfer n (fun s => H + E s) = R.operatorTransfer n (fun _
=> H) + R.linearResponse n H E + R.driftRemainder n H E`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_driftRemainder_le`.
-/
def driftRemainder (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) : Matrix d d ℝ :=
  R.contract (higherOrder (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (E s)) n)

/--
Exact expansion over all sets of insertion times (Appendix A.2).

Exact identity `R.operatorTransfer n (fun s => H + E s) = ∑ S ∈ (Finset.range n).powerset,
R.contract (insertionTerm (fun s => R.operatorStep s H) (fun s => R.operatorInsertion s (E s))
n S)`.

Use: `chebyshev1.JacobiData.finiteDrift_words` rewrites with this identity to establish
exact identity `(J.realization I).operatorTransfer N (fun s => H + E s) = ∑ times ∈
(Finset.range N).powerset, ((-(2 / I.delta)) ^ times.card / J.den I N) • J.operatorWord I H E N
times`.

Article: chebyshev1, Corollary 5.3 via
`chebyshev1.SineJacobi.driftOrder_static_attained`.

Proof: Use the identities/estimates `chebyshev1.Realization.operatorStep_add`,
`chebyshev1.orderedProduct_add_expansion` with the arguments shown in the proof.
-/
theorem operatorTransfer_expansion (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    R.operatorTransfer n (fun s => H + E s) =
      ∑ S ∈ (Finset.range n).powerset,
        R.contract (insertionTerm (fun s => R.operatorStep s H)
          (fun s => R.operatorInsertion s (E s)) n S) := by
  -- Use the identities/estimates `chebyshev1.Realization.operatorStep_add`,
  -- `chebyshev1.orderedProduct_add_expansion` with the arguments shown in the proof.
  unfold operatorTransfer
  simp_rw [operatorStep_add]
  change R.contractLinear _ = _
  rw [orderedProduct_add_expansion, map_sum]
  rfl

/--
Proposition 1.3: an exact identity, without any smallness assumption on the drift.

Exact identity `R.operatorTransfer n (fun s => H + E s) = R.operatorTransfer n (fun _ => H) +
R.linearResponse n H E + R.driftRemainder n H E`.

Use: `chebyshev1.Realization.finiteDrift_polynomial_decomposition` rewrites with this
identity to establish the identity `R.operatorTransfer n (fun s => H + E s) =
Polynomial.aeval H (R.residualPolynomial n) + R.linearResponse n H E + R.driftRemainder n H E`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.static_shift_attained`.

Proof: Use the identities/estimates `chebyshev1.Realization.operatorStep_add`,
`chebyshev1.orderedProduct_add_decomposition` with the arguments shown in the proof.
-/
theorem operatorTransfer_decomposition (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    R.operatorTransfer n (fun s => H + E s) =
      R.operatorTransfer n (fun _ => H) + R.linearResponse n H E + R.driftRemainder n H E := by
  -- Use the identities/estimates `chebyshev1.Realization.operatorStep_add`,
  -- `chebyshev1.orderedProduct_add_decomposition` with the arguments shown in the proof.
  unfold operatorTransfer linearResponse driftRemainder
  simp_rw [operatorStep_add]
  change R.contractLinear _ = R.contractLinear _ + R.contractLinear _ + R.contractLinear _
  rw [orderedProduct_add_decomposition, map_add, map_add]

/--
The first variation is the sum of causally ordered single insertions.

Exact identity `R.linearResponse n H E = ∑ s ∈ Finset.range n, R.contract (orderedProduct (fun
i => R.operatorStep (s + 1 + i) H) (n - (s + 1)) * R.operatorInsertion s (E s) * orderedProduct
(fun i => R.operatorStep i H) s)`.

Use: `chebyshev1.Realization.linearResponse_coordinates` rewrites with this identity to
establish exact identity `R.linearResponse N (Qᵀ * H * Q) (fun s => Qᵀ * E s * Q) = Qᵀ *
R.linearResponse N H E * Q`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.firstVariation_eq_sum` with the arguments
shown in the proof.
-/
theorem linearResponse_eq_sum (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) :
    R.linearResponse n H E = ∑ s ∈ Finset.range n,
      R.contract (orderedProduct (fun i => R.operatorStep (s + 1 + i) H) (n - (s + 1)) *
        R.operatorInsertion s (E s) * orderedProduct (fun i => R.operatorStep i H) s) := by
  -- Use the identities/estimates `chebyshev1.firstVariation_eq_sum` with the arguments
  -- shown in the proof.
  unfold linearResponse
  change R.contractLinear _ = _
  rw [firstVariation_eq_sum, map_sum]
  rfl

/--
Lemma 1.1: the insertion sum is the actual derivative at zero drift.

The actual derivative at the stated point: `HasDerivAt (fun δ : ℝ => R.operatorTransfer n (fun
s => H + δ • B s)) (R.linearResponse n H B) 0`.

Use: `chebyshev1.Realization.deriv_operatorTransfer` uses this derivative formula to
establish exact identity `deriv (fun δ : ℝ => R.operatorTransfer n (fun s => H + δ • B s)) 0 =
R.linearResponse n H B`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `chebyshev1.hasDerivAt_orderedProduct_affine`,
`chebyshev1.Realization.operatorStep_add`,
`chebyshev1.Realization.operatorInsertion_smul` with the arguments shown in the proof.
-/
theorem hasDerivAt_operatorTransfer (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) :
    HasDerivAt (fun δ : ℝ => R.operatorTransfer n (fun s => H + δ • B s))
      (R.linearResponse n H B) 0 := by
  -- Use the identities/estimates `chebyshev1.hasDerivAt_orderedProduct_affine`,
  -- `chebyshev1.Realization.operatorStep_add`,
  -- `chebyshev1.Realization.operatorInsertion_smul` with the arguments shown in the proof.
  let L := (R.contractLinear (d := d)).toContinuousLinearMap
  have hp := hasDerivAt_orderedProduct_affine (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (B s)) n
  have h := L.hasFDerivAt.comp_hasDerivAt 0 hp
  convert! h using 1
  simp [L, operatorTransfer, operatorStep_add, operatorInsertion_smul,
      Function.comp_def]

/--
Exact identity `deriv (fun δ : ℝ => R.operatorTransfer n (fun s => H + δ • B s)) 0 =
R.linearResponse n H B`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Lemma 1.1.

Proof: Use the identities/estimates `chebyshev1.Realization.hasDerivAt_operatorTransfer`
with the arguments shown in the proof.
-/
theorem deriv_operatorTransfer (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) :
    deriv (fun δ : ℝ => R.operatorTransfer n (fun s => H + δ • B s)) 0 =
      R.linearResponse n H B :=
  (R.hasDerivAt_operatorTransfer n H B).deriv

end
end chebyshev1.Realization

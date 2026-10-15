import «2606.16671v2».Realization.Expansion
import «2606.16671v2».Algebra.Multilinear

/-!
Article: 2606.16671v2, Proposition 1.3.
The full output is a degree-at-most-`n` polynomial in the scalar drift size.
Use: `«2606.16671v2».Realization.operatorTransfer_affine_by_degree` feeds
`«2606.16671v2».JacobiData.operatorTransfer_driftOrders` (operator Transfer drift Orders).
Proof chain: `«2606.16671v2».JacobiData.operatorTransfer_driftOrders` — 2606.16671v2, Theorem 4.3;
All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2».Realization

open scoped BigOperators
noncomputable section

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/--
Constructs `operatorInsertionLinear` of type `Matrix d d ℝ →ₗ[ℝ] Matrix (ι × d) (ι × d) ℝ` by
the displayed record fields. Data fields specify the construction; proof fields discharge its
required properties.

Use: `«2606.16671v2».Realization.driftTermMultilinear` uses this definition in the displayed
construction of `driftTermMultilinear`. Its inputs and component formulas are fixed by that
definition.

Article: 2606.16671v2, Proposition 1.3.
-/
def operatorInsertionLinear (R : Realization ι) (s : ℕ) :
    Matrix d d ℝ →ₗ[ℝ] Matrix (ι × d) (ι × d) ℝ where
  toFun := R.operatorInsertion s
  map_add' := R.operatorInsertion_add s
  map_smul' := R.operatorInsertion_smul s

/--
The contribution indexed by `S` is multilinear in exactly those Hessian directions.

Use: `«2606.16671v2».Realization.driftTermMultilinear_apply` rewrites with this definition to
establish exact identity `R.driftTermMultilinear n H S hS (fun s => E s.val) = R.contract
(insertionTerm (fun s => R.operatorStep s H) (fun s => R.operatorInsertion s (E s)) n S)`.

Article: 2606.16671v2, Proposition 1.3.
-/
def driftTermMultilinear (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    MultilinearMap ℝ (fun _ : S => Matrix d d ℝ) (Matrix d d ℝ) :=
  R.contractLinear.compMultilinearMap
    ((insertionMultilinear (K := ℝ) (fun s => R.operatorStep s H) n S hS).compLinearMap
      (fun s => R.operatorInsertionLinear s.val))

/--
Exact identity `R.driftTermMultilinear n H S hS (fun s => E s.val) = R.contract (insertionTerm
(fun s => R.operatorStep s H) (fun s => R.operatorInsertion s (E s)) n S)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2606.16671v2, Proposition 1.3.

Proof: Use the identities/estimates `«2606.16671v2».insertionMultilinear_apply` with the
arguments shown in the proof.
-/
theorem driftTermMultilinear_apply (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (E : ℕ → Matrix d d ℝ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    R.driftTermMultilinear n H S hS (fun s => E s.val) =
      R.contract (insertionTerm (fun s => R.operatorStep s H)
        (fun s => R.operatorInsertion s (E s)) n S) := by
  -- Use the identities/estimates `«2606.16671v2».insertionMultilinear_apply` with the
  -- arguments shown in the proof.
  simp only [driftTermMultilinear, LinearMap.compMultilinearMap_apply,
    MultilinearMap.compLinearMap_apply, operatorInsertionLinear]
  change R.contractLinear
    (insertionMultilinear (K := ℝ) (fun s => R.operatorStep s H) n S hS
      (fun s => R.operatorInsertion s.val (E s.val))) = _
  rw [insertionMultilinear_apply (K := ℝ) (fun s => R.operatorStep s H)
    (fun s => R.operatorInsertion s (E s)) n S hS]
  rfl

/--
The full output is a degree-at-most-`n` polynomial in the scalar drift size.

Exact identity `R.operatorTransfer n (fun s => H + δ • B s) = ∑ k ∈ Finset.range (n + 1), δ ^ k
• R.contract (degreeTerm (fun s => R.operatorStep s H) (fun s => R.operatorInsertion s (B s)) n
k)`.

Use: `«2606.16671v2».JacobiData.operatorTransfer_driftOrders` uses this identity to establish
exact identity `(J.realization I).operatorTransfer N (fun s => H + E s) = ∑ k ∈ Finset.range (N
+ 1), J.driftOrder I N k H E`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.operatorStep_add`,
`«2606.16671v2».Realization.operatorInsertion_smul`,
`«2606.16671v2».orderedProduct_affine_by_degree` with the arguments shown in the proof.
-/
theorem operatorTransfer_affine_by_degree (R : Realization ι) (n : ℕ) (H : Matrix d d ℝ)
    (B : ℕ → Matrix d d ℝ) (δ : ℝ) :
    R.operatorTransfer n (fun s => H + δ • B s) =
      ∑ k ∈ Finset.range (n + 1), δ ^ k •
        R.contract (degreeTerm (fun s => R.operatorStep s H)
          (fun s => R.operatorInsertion s (B s)) n k) := by
  -- Use the identities/estimates `«2606.16671v2».Realization.operatorStep_add`,
  -- `«2606.16671v2».Realization.operatorInsertion_smul`,
  -- `«2606.16671v2».orderedProduct_affine_by_degree` with the arguments shown in the proof.
  unfold operatorTransfer
  simp_rw [operatorStep_add, operatorInsertion_smul]
  change R.contractLinear _ = _
  rw [orderedProduct_affine_by_degree, map_sum]
  simp only [map_smul, contractLinear_apply]

end
end «2606.16671v2».Realization

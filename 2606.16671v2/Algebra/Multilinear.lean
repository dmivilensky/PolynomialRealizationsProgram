import «2606.16671v2».Algebra.OrderedProduct
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
Article: 2606.16671v2, Proposition 1.3.
The affine causal product is a finite polynomial in the drift scale.
Use: `«2606.16671v2».orderedProduct_affine_by_degree` feeds
`«2606.16671v2».Realization.operatorTransfer_affine_by_degree` (The full output is a
degree-at-most-`n` polynomial in the scalar drift size).
Proof chain: `«2606.16671v2».JacobiData.operatorTransfer_driftOrders` — 2606.16671v2, Theorem 4.3;
All insertion orders, partition bounds, finite/cosh bounds and attainment.
Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in selected
factors. The needed form is proved here.
-/
namespace «2606.16671v2»

noncomputable section

variable {K A : Type*} [CommSemiring K] [Semiring A] [Algebra K A]

/--
Factors with independent variables only at the selected times.

Use: `«2606.16671v2».insertionMultilinear` uses this definition in the displayed construction
of `insertionMultilinear`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
def selectedFactors (C : ℕ → A) (S : Finset ℕ) (v : S → A) (i : ℕ) : A :=
  if h : i ∈ S then v ⟨i, h⟩ else C i

omit [Semiring A] in
/--
Exact identity `selectedFactors C S (Function.update v s a) = Function.update (selectedFactors
C S v) s.val a`.

Use: `«2606.16671v2».insertionMultilinear` uses this identity in the displayed construction of
`insertionMultilinear`. Its inputs and component formulas are fixed by that definition.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.

Proof: Separate `i = s.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem selectedFactors_update (C : ℕ → A) (S : Finset ℕ) (v : S → A)
    (s : S) (a : A) :
    selectedFactors C S (Function.update v s a) =
      Function.update (selectedFactors C S v) s.val a := by
  -- Separate `i = s.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  funext i
  by_cases hi : i = s.val
  · subst i
    simp [selectedFactors]
  · by_cases hS : i ∈ S
    · have hne : (⟨i, hS⟩ : S) ≠ s := by
        intro h
        exact hi (congrArg Subtype.val h)
      simp [selectedFactors, hS, hi, hne]
    · simp [selectedFactors, hS, hi]

/--
A term with `S.card` insertions is an actual `S`-indexed multilinear map.

Use: `«2606.16671v2».insertionMultilinear_apply` uses this definition to establish exact
identity `insertionMultilinear (K := K) C n S hS (fun s => D s.val) = insertionTerm C D n S`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.
-/
def insertionMultilinear (C : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) : MultilinearMap K (fun _ : S => A) A :=
  MultilinearMap.mk' (fun v => orderedProduct (selectedFactors C S v) n)
    (fun v s a b => by
      have hs : s.val < n := Finset.mem_range.mp (hS s.property)
      simp only [selectedFactors_update, orderedProduct_update _ _ hs]
      simp [mul_add, add_mul])
    (fun v s c a => by
      have hs : s.val < n := Finset.mem_range.mp (hS s.property)
      simp only [selectedFactors_update, orderedProduct_update _ _ hs]
      simp)

/--
Exact identity `insertionMultilinear (K := K) C n S hS (fun s => D s.val) = insertionTerm C D n
S`.

Use: `«2606.16671v2».insertionTerm_smul` rewrites with this identity to establish exact
identity `insertionTerm C (fun s => c • D s) n S = c ^ S.card • insertionTerm C D n S`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.

Proof: Use the identities/estimates `«2606.16671v2».orderedProduct_congr` with the arguments
shown in the proof.
-/
theorem insertionMultilinear_apply (C D : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    insertionMultilinear (K := K) C n S hS (fun s => D s.val) = insertionTerm C D n S := by
  unfold insertionMultilinear insertionTerm
  apply orderedProduct_congr
  intro i _
  simp [selectedFactors]

/--
Scaling all directions multiplies a term by exactly the insertion-count power.

Exact identity `insertionTerm C (fun s => c • D s) n S = c ^ S.card • insertionTerm C D n S`.

Use: `«2606.16671v2».degreeTerm_smul` rewrites with this identity to establish the identity
`degreeTerm C (fun s => c • D s) n k = c ^ k • degreeTerm C D n k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.

Proof: Use the identities/estimates `«2606.16671v2».insertionMultilinear_apply` with the
arguments shown in the proof.
-/
theorem insertionTerm_smul (C D : ℕ → A) (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) (c : K) :
    insertionTerm C (fun s => c • D s) n S = c ^ S.card • insertionTerm C D n S := by
  rw [← insertionMultilinear_apply (K := K) C (fun s => c • D s) n S hS,
    ← insertionMultilinear_apply (K := K) C D n S hS]
  simpa using (insertionMultilinear (K := K) C n S hS).map_smul_univ
    (fun _ => c) (fun s => D s.val)

/--
Exact identity `degreeTerm C (fun s => c • D s) n k = c ^ k • degreeTerm C D n k`.

Use: `«2606.16671v2».orderedProduct_affine_by_degree` rewrites with this identity to establish
exact identity `orderedProduct (fun s => C s + c • D s) n = ∑ k ∈ Finset.range (n + 1), c ^ k •
degreeTerm C D n k`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem degreeTerm_smul (C D : ℕ → A) (n k : ℕ) (c : K) :
    degreeTerm C (fun s => c • D s) n k = c ^ k • degreeTerm C D n k := by
  unfold degreeTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  rw [insertionTerm_smul C D n S hsub, hcard]

/--
The affine causal product is a finite polynomial in the drift scale.

Exact identity `orderedProduct (fun s => C s + c • D s) n = ∑ k ∈ Finset.range (n + 1), c ^ k •
degreeTerm C D n k`.

Use: `«2606.16671v2».Realization.operatorTransfer_affine_by_degree` rewrites with this identity
to establish the identity `R.operatorTransfer n (fun s => H + δ • B s) = ∑ k ∈ Finset.range
(n + 1), δ ^ k • R.contract (degreeTerm (fun s => R.operatorStep s H) (fun s =>
R.operatorInsertion s (B s)) n k)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_finiteDrift_le`.

Source: mathlib, Mathlib.LinearAlgebra.Multilinear.Basic — multilinearity of products in
selected factors.

Proof: Use the identities/estimates `«2606.16671v2».orderedProduct_add_by_degree`,
`«2606.16671v2».degreeTerm_smul` with the arguments shown in the proof.
-/
theorem orderedProduct_affine_by_degree (C D : ℕ → A) (n : ℕ) (c : K) :
    orderedProduct (fun s => C s + c • D s) n =
      ∑ k ∈ Finset.range (n + 1), c ^ k • degreeTerm C D n k := by
  rw [orderedProduct_add_by_degree]
  simp_rw [degreeTerm_smul]

end
end «2606.16671v2»

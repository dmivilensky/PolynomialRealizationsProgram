import «2606.16671v2».Realization.Expansion

/-!
Article: 2606.16671v2, Lemma 1.1.
Lemma 1.1 on an arbitrary spectral pair, including repeated eigenspaces.
Use: `«2606.16671v2».Realization.spectralPair_linearResponse` feeds
`«2606.16671v2».Realization.diagonal_linearResponse_entry` (First variation in an orthonormal
eigenbasis, entry by entry).
Proof chain: `«2606.16671v2».Realization.static_shift_lower_bounds_general` — 2606.16671v2, Theorem
4.3; All insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace «2606.16671v2».Realization

open scoped BigOperators Kronecker
noncomputable section

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

omit [DecidableEq ι] in
/--
Exact identity `(M ⊗ₖ Proj) * R.operatorStep s H = (M * R.scalarStep s lam) ⊗ₖ Proj`.

Use: `«2606.16671v2».Realization.kronecker_left_orderedProduct` rewrites with this identity to
establish exact identity `(M ⊗ₖ Proj) * orderedProduct (fun i => R.operatorStep (a + i) H) n =
(M * orderedProduct (fun i => R.scalarStep (a + i) lam) n) ⊗ₖ Proj`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem kronecker_left_operatorStep (R : Realization ι) (s : ℕ)
    (M : Matrix ι ι ℝ) (H Proj : Matrix d d ℝ) (lam : ℝ) (h : Proj * H = lam • Proj) :
    (M ⊗ₖ Proj) * R.operatorStep s H = (M * R.scalarStep s lam) ⊗ₖ Proj := by
  rw [operatorStep, Matrix.mul_sub, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.kronecker_smul,
    scalarStep, Matrix.mul_sub, Matrix.mul_smul]
  ext ⟨i, x⟩ ⟨j, y⟩
  simp [Matrix.kroneckerMap_apply, sub_mul, mul_assoc]

omit [DecidableEq ι] in
/--
Exact identity `R.operatorStep s H * (M ⊗ₖ Proj) = (R.scalarStep s nu * M) ⊗ₖ Proj`.

Use: `«2606.16671v2».Realization.orderedProduct_kronecker_right` rewrites with this identity to
establish exact identity `orderedProduct (fun i => R.operatorStep (a + i) H) n * (M ⊗ₖ Proj) =
(orderedProduct (fun i => R.scalarStep (a + i) nu) n * M) ⊗ₖ Proj`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem operatorStep_kronecker_right (R : Realization ι) (s : ℕ)
    (M : Matrix ι ι ℝ) (H Proj : Matrix d d ℝ) (nu : ℝ) (h : H * Proj = nu • Proj) :
    R.operatorStep s H * (M ⊗ₖ Proj) = (R.scalarStep s nu * M) ⊗ₖ Proj := by
  rw [operatorStep, Matrix.sub_mul, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, h, Matrix.one_mul, Matrix.kronecker_smul,
    scalarStep, Matrix.sub_mul, Matrix.smul_mul]
  ext ⟨i, x⟩ ⟨j, y⟩
  simp [Matrix.kroneckerMap_apply, sub_mul, mul_assoc]

/--
Exact identity `(M ⊗ₖ Proj) * orderedProduct (fun i => R.operatorStep (a + i) H) n = (M *
orderedProduct (fun i => R.scalarStep (a + i) lam) n) ⊗ₖ Proj`.

Use: `«2606.16671v2».Realization.spectralPair_singleInsertion` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Induct on `n` while keeping `M` arbitrary; the recursive step uses the
previous-stage assertion.
-/
theorem kronecker_left_orderedProduct (R : Realization ι) (a n : ℕ)
    (M : Matrix ι ι ℝ) (H Proj : Matrix d d ℝ) (lam : ℝ) (h : Proj * H = lam • Proj) :
    (M ⊗ₖ Proj) * orderedProduct (fun i => R.operatorStep (a + i) H) n =
      (M * orderedProduct (fun i => R.scalarStep (a + i) lam) n) ⊗ₖ Proj := by
  -- Induct on `n` while keeping `M` arbitrary; the recursive step uses the previous-stage
  -- assertion.
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
    rw [orderedProduct_succ, ← Matrix.mul_assoc, R.kronecker_left_operatorStep _ _ H Proj lam h,
      ih, orderedProduct_succ, Matrix.mul_assoc]

/--
Exact identity `orderedProduct (fun i => R.operatorStep (a + i) H) n * (M ⊗ₖ Proj) =
(orderedProduct (fun i => R.scalarStep (a + i) nu) n * M) ⊗ₖ Proj`.

Use: `«2606.16671v2».Realization.spectralPair_singleInsertion` uses this identity to establish
the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem orderedProduct_kronecker_right (R : Realization ι) (a n : ℕ)
    (M : Matrix ι ι ℝ) (H Proj : Matrix d d ℝ) (nu : ℝ) (h : H * Proj = nu • Proj) :
    orderedProduct (fun i => R.operatorStep (a + i) H) n * (M ⊗ₖ Proj) =
      (orderedProduct (fun i => R.scalarStep (a + i) nu) n * M) ⊗ₖ Proj := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orderedProduct_succ, Matrix.mul_assoc, ih,
      R.operatorStep_kronecker_right _ _ H Proj nu h, orderedProduct_succ, Matrix.mul_assoc]

omit [DecidableEq ι] [Fintype d] [DecidableEq d] in
/--
Exact identity `R.contract (M ⊗ₖ B) = R.scalarContract M • B`.

Use: `«2606.16671v2».Realization.spectralPair_singleInsertion` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem contract_kronecker (R : Realization ι) (M : Matrix ι ι ℝ) (B : Matrix d d ℝ) :
    R.contract (M ⊗ₖ B) = R.scalarContract M • B := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  ext x y
  simp only [contract, scalarContract, Matrix.kroneckerMap_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq d] in
/--
Exact identity `R.contract (((1 : Matrix ι ι ℝ) ⊗ₖ A) * M) = A * R.contract M`.

Use: `«2606.16671v2».Realization.spectralPair_singleInsertion` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem contract_kronecker_left (R : Realization ι)
    (M : Matrix (ι × d) (ι × d) ℝ) (A : Matrix d d ℝ) :
    R.contract (((1 : Matrix ι ι ℝ) ⊗ₖ A) * M) = A * R.contract M := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  ext x y
  simp only [contract, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  ring

omit [DecidableEq d] in
/--
Exact identity `R.contract (M * ((1 : Matrix ι ι ℝ) ⊗ₖ A)) = R.contract M * A`.

Use: `«2606.16671v2».Realization.spectralPair_singleInsertion` rewrites with this identity to
establish the identity stated in that declaration.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem contract_kronecker_right (R : Realization ι)
    (M : Matrix (ι × d) (ι × d) ℝ) (A : Matrix d d ℝ) :
    R.contract (M * ((1 : Matrix ι ι ℝ) ⊗ₖ A)) = R.contract M * A := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  ext x y
  simp only [contract, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro z _
  ring

/--
The spectral block of one insertion is exactly `K_s(lam, nu)` times that of `E`.

Use: `«2606.16671v2».Realization.spectralPair_linearResponse` uses this identity to establish
exact identity `Projlam * R.linearResponse n H E * Projnu = ∑ s ∈ Finset.range n, R.kernel n s
lam nu • (Projlam * E s * Projnu)`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Use the identities/estimates `«2606.16671v2».Realization.contract_kronecker_left`,
`«2606.16671v2».Realization.contract_kronecker_right`,
`«2606.16671v2».Realization.kronecker_left_orderedProduct` with the arguments shown in the
proof.
-/
theorem spectralPair_singleInsertion (R : Realization ι) (n s : ℕ)
    (H E Projlam Projnu : Matrix d d ℝ) (lam nu : ℝ)
    (hlam : Projlam * H = lam • Projlam) (hnu : H * Projnu = nu • Projnu) :
    Projlam * R.contract
      (orderedProduct (fun i => R.operatorStep (s + 1 + i) H) (n - (s + 1)) *
        R.operatorInsertion s E * orderedProduct (fun i => R.operatorStep i H) s) * Projnu =
      R.kernel n s lam nu • (Projlam * E * Projnu) := by
  -- Use the identities/estimates `«2606.16671v2».Realization.contract_kronecker_left`,
  -- `«2606.16671v2».Realization.contract_kronecker_right`,
  -- `«2606.16671v2».Realization.kronecker_left_orderedProduct` with the arguments shown in the
  -- proof.
  rw [← contract_kronecker_left, ← contract_kronecker_right]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    R.kronecker_left_orderedProduct (s + 1) (n - (s + 1)) 1 H Projlam lam hlam,
    Matrix.one_mul]
  have hright := R.orderedProduct_kronecker_right 0 s 1 H Projnu nu hnu
  simp only [Nat.zero_add, Matrix.mul_one] at hright
  simp only [Matrix.mul_assoc]
  rw [hright]
  simp only [operatorInsertion, Matrix.mul_neg,
    Matrix.neg_mul, ← Matrix.mul_kronecker_mul]
  change R.contractLinear (-(_ ⊗ₖ _)) = _
  rw [map_neg, contractLinear_apply, contract_kronecker]
  simp [kernel, Matrix.mul_assoc]

/--
Lemma 1.1 on an arbitrary spectral pair, including repeated eigenspaces.

Exact identity `Projlam * R.linearResponse n H E * Projnu = ∑ s ∈ Finset.range n, R.kernel n s
lam nu • (Projlam * E s * Projnu)`.

Use: `«2606.16671v2».Realization.diagonal_linearResponse_entry` uses this identity to establish
exact identity `R.linearResponse N (Matrix.diagonal eig) E i j = ∑ s ∈ Finset.range N, R.kernel
N s (eig i) (eig j) * E s i j`.

Article: 2606.16671v2, Corollary 4.4 via `«2606.16671v2».Prefix.opNorm_linearResponse_le`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem spectralPair_linearResponse (R : Realization ι) (n : ℕ)
    (H Projlam Projnu : Matrix d d ℝ) (E : ℕ → Matrix d d ℝ) (lam nu : ℝ)
    (hlam : Projlam * H = lam • Projlam) (hnu : H * Projnu = nu • Projnu) :
    Projlam * R.linearResponse n H E * Projnu =
      ∑ s ∈ Finset.range n, R.kernel n s lam nu • (Projlam * E s * Projnu) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [linearResponse_eq_sum, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  exact R.spectralPair_singleInsertion n s H (E s) Projlam Projnu lam nu hlam hnu

end
end «2606.16671v2».Realization

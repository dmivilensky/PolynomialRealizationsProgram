import chebyshev1.Realization.Normalization
import chebyshev1.Realization.Polynomial

/-! Physical gradient execution and its affine change to error coordinates. -/
namespace chebyshev1.Realization
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Kronecker Matrix
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The coefficients of a translated stationary state in each memory slot. -/
structure AffineConsistent (R : chebyshev1.Realization ι) (N : ℕ) where
  center : ℕ → ι → ℝ
  initial : center 0 = R.b
  transition : ∀ s < N, (R.P s).mulVec (center s) = center (s+1)
  query : ∀ s < N, dotProduct (R.q s) (center s) = 1
  terminal : dotProduct R.readout (center N) = 1

def memoryVector (c : ι → ℝ) (x : d → ℝ) : ι × d → ℝ :=
  fun p => c p.1 * x p.2

def queryVector (R : chebyshev1.Realization ι) (s : ℕ) (Y : ι × d → ℝ) : d → ℝ :=
  fun x => ∑ i, R.q s i * Y (i,x)

/-- A literal gradient query on the translated quadratic with Hessian H. -/
def physicalStep (R : chebyshev1.Realization ι) (s : ℕ) (H : Matrix d d ℝ)
    (a : d → ℝ) (Y : ι × d → ℝ) : ι × d → ℝ :=
  fun p => (∑ j, R.P s p.1 j * Y (j,p.2)) -
    R.g s p.1 * H.mulVec (R.queryVector s Y - a) p.2

def physicalMemory (R : chebyshev1.Realization ι) (H : ℕ → Matrix d d ℝ)
    (a x0 : d → ℝ) : ℕ → ι × d → ℝ
  | 0 => memoryVector R.b x0
  | n+1 => R.physicalStep n (H n) a (R.physicalMemory H a x0 n)

def physicalOutput (R : chebyshev1.Realization ι) (H : ℕ → Matrix d d ℝ)
    (a x0 : d → ℝ) (N : ℕ) : d → ℝ :=
  fun x => ∑ i, R.readout i * R.physicalMemory H a x0 N (i,x)

omit [DecidableEq ι] in
private theorem operatorStep_apply (R : chebyshev1.Realization ι) (s : ℕ)
    (H : Matrix d d ℝ) (Y : ι × d → ℝ) (i : ι) (x : d) :
    (R.operatorStep s H).mulVec Y (i,x) =
      (∑ j, R.P s i j * Y (j,x)) - R.g s i *
        (H.mulVec (R.queryVector s Y)) x := by
  simp only [Matrix.mulVec_apply_eq_sum, operatorStep, Matrix.sub_apply,
    Fintype.sum_prod_type, Matrix.kronecker_apply, queryFactor,
    Matrix.vecMulVec_apply, Matrix.one_apply, queryVector, sub_mul,
    Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

omit [DecidableEq ι] in
theorem physicalStep_eq_operator_add (R : chebyshev1.Realization ι) (s : ℕ)
    (H : Matrix d d ℝ) (a : d → ℝ) (Y : ι × d → ℝ) :
    R.physicalStep s H a Y = (R.operatorStep s H).mulVec Y +
      memoryVector (R.g s) (H.mulVec a) := by
  ext ⟨i,x⟩
  simp only [physicalStep, Pi.add_apply]
  rw [operatorStep_apply, Matrix.mulVec_sub]
  simp only [memoryVector, Pi.sub_apply]
  ring

omit [DecidableEq ι] in
theorem operatorStep_memoryVector (R : chebyshev1.Realization ι) (s : ℕ)
    (H : Matrix d d ℝ) (c : ι → ℝ) (a : d → ℝ) :
    (R.operatorStep s H).mulVec (memoryVector c a) =
      memoryVector ((R.P s).mulVec c) a -
        memoryVector (fun i => R.g s i * dotProduct (R.q s) c) (H.mulVec a) := by
  have hquery : R.queryVector s (memoryVector c a) = dotProduct (R.q s) c • a := by
    ext x
    simp only [queryVector, memoryVector, Pi.smul_apply, smul_eq_mul, dotProduct]
    simp_rw [← mul_assoc]
    rw [Finset.sum_mul]
  ext ⟨i,x⟩
  rw [operatorStep_apply, hquery, Matrix.mulVec_smul]
  simp only [memoryVector, Matrix.mulVec_apply_eq_sum, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]

theorem physicalMemory_affine (R : chebyshev1.Realization ι) {N : ℕ}
    (h : R.AffineConsistent N) (H : ℕ → Matrix d d ℝ) (a x0 : d → ℝ)
    (n : ℕ) (hn : n ≤ N) :
    R.physicalMemory H a x0 n =
      (orderedProduct (fun s => R.operatorStep s (H s)) n).mulVec
        (memoryVector R.b (x0-a)) + memoryVector (h.center n) a := by
  induction n with
  | zero =>
    rw [physicalMemory, orderedProduct, Matrix.one_mulVec, h.initial]
    ext ⟨i,x⟩
    simp only [memoryVector, Pi.add_apply, Pi.sub_apply]
    ring
  | succ n ih =>
    rw [physicalMemory, physicalStep_eq_operator_add, ih (by omega),
      Matrix.mulVec_add, operatorStep_memoryVector, h.transition n (by omega),
      h.query n (by omega), orderedProduct_succ, Matrix.mulVec_mulVec]
    simp only [mul_one]
    abel

omit [DecidableEq ι] [DecidableEq d] in
private theorem contract_mulVec (R : chebyshev1.Realization ι)
    (M : Matrix (ι × d) (ι × d) ℝ) (v : d → ℝ) (x : d) :
    (R.contract M).mulVec v x =
      ∑ i, R.readout i * M.mulVec (memoryVector R.b v) (i,x) := by
  simp only [contract, Matrix.mulVec, dotProduct, memoryVector, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The article's physical error-transfer formula, with every affine consistency
condition explicit and with arbitrary time-dependent Hessians. -/
theorem physicalOutput_error (R : chebyshev1.Realization ι) {N : ℕ}
    (h : R.AffineConsistent N) (H : ℕ → Matrix d d ℝ) (a x0 : d → ℝ) :
    R.physicalOutput H a x0 N - a =
      (R.operatorTransfer N H).mulVec (x0-a) := by
  ext x
  change (∑ i, R.readout i * R.physicalMemory H a x0 N (i,x)) - a x = _
  rw [R.physicalMemory_affine h H a x0 N le_rfl]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, memoryVector]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  rw [show (∑ i, R.readout i * h.center N i) = 1 from h.terminal]
  rw [one_mul, add_sub_cancel_right, operatorTransfer, contract_mulVec]

omit [Fintype d] [DecidableEq d] in
theorem AffineConsistent.center_eq_product {R : chebyshev1.Realization ι} {N : ℕ}
    (h : R.AffineConsistent N) (n : ℕ) (hn : n≤N) :
    h.center n = (orderedProduct R.P n).mulVec R.b := by
  induction n with
  | zero => simpa only [orderedProduct, Matrix.one_mulVec] using h.initial
  | succ n ih =>
    rw [← h.transition n (by omega), ih (by omega), orderedProduct_succ,
      Matrix.mulVec_mulVec]

omit [Fintype d] [DecidableEq d] in
theorem AffineConsistent.residual_zero {R : chebyshev1.Realization ι} {N : ℕ}
    (h : R.AffineConsistent N) : (R.residualPolynomial N).eval 0 = 1 := by
  rw [R.residualPolynomial_eval]
  have hc := h.terminal
  rw [h.center_eq_product N le_rfl] at hc
  simpa only [scalarTransfer, scalarStep, zero_smul, sub_zero, scalarContract,
    Matrix.mulVec_apply_eq_sum, dotProduct, Finset.mul_sum, mul_assoc] using hc

/-- The residual polynomial acts on the actual physical error of a translated quadratic. -/
theorem physicalOutput_quadratic_error (R : chebyshev1.Realization ι) {N : ℕ}
    (h : R.AffineConsistent N) (H : Matrix d d ℝ) (a x0 : d → ℝ) :
    R.physicalOutput (fun _ => H) a x0 N - a =
      (Polynomial.aeval H (R.residualPolynomial N)).mulVec (x0-a) := by
  rw [R.physicalOutput_error h, R.operatorTransfer_eq_aeval]

end
end chebyshev1.Realization

import krylov.Functions.NativeRFCSymmetry
import krylov.Functions.RFCPhysicalCompact
import krylov.Functions.FCOwnCanonical

/-!
Article: main_krylov, thm:Htransfer, exact native ordinary RFC physical chart.
Use: place actual symmetric search and correction Hessian averages into the
existing finite symmetric source space, including the genuine drifting first
secant. Source: the Euclidean operator/matrix isometry and exact finite oracle
prefix dependence; no asymptotic operator scenario is substituted.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction krylov.Envelope krylov.Variation
open scoped Matrix.Norms.L2Operator
variable {k n : ℕ}

/-- The actual physical matrix/operator correspondence preserves its genuine
spectral norm. Article: main_krylov, thm:Htransfer. -/
theorem physicalOperatorMatrix_norm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖physicalOperatorMatrix A‖=‖A‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  exact congrArg norm (physicalOperatorMatrix_operator A)

/-- A genuine symmetric physical operator gives a true symmetric matrix.
Article: main_krylov, thm:Htransfer. -/
theorem physicalOperatorMatrix_symmetric (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : A.toLinearMap.IsSymmetric) : (physicalOperatorMatrix A).IsSymm := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (cgOperator (physicalOperatorMatrix A)).toLinearMap.IsSymmetric
  rw [physicalOperatorMatrix_operator]
  exact hA

/-- All actual native symmetric segment operators in one exact finite source
chart. The sole unused correction slot is filled with zero.
Article: main_krylov, thm:Htransfer. -/
def rfcPhysicalDataOfOperators (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric)
    (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric) : RFCPhysicalData k := by
  classical
  refine ⟨(fun j=>physicalOperatorMatrix (A j.val-cgOperator base),
    fun j=>if h : j.val<k+1 then physicalOperatorMatrix (B j.val-cgOperator base) else 0),?_,?_⟩
  · intro j
    exact physicalOperatorMatrix_symmetric _ ((hA j.val j.isLt).sub hQ)
  · intro j
    change (if h : j.val<k+1 then physicalOperatorMatrix (B j.val-cgOperator base) else 0).IsSymm
    split_ifs with hj
    · exact physicalOperatorMatrix_symmetric _ ((hB j.val hj).sub hQ)
    · exact Matrix.isSymm_zero

/-- The finite symmetric native chart reproduces every real physical search
operator that the actual cycle executes. Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalDataOfOperators_search (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric)
    (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric) (i : ℕ) (hi : i<k+1) :
    rfcPhysicalSearch base (rfcPhysicalDataOfOperators base hQ A B hA hB) i=A i := by
  simp only [rfcPhysicalSearch,rfcPhysicalDataOfOperators,matrixSequenceExtension,dite_eq_left hi,
    cgOperator,map_add]
  change cgOperator base+cgOperator (physicalOperatorMatrix (A i-cgOperator base))=A i
  rw [physicalOperatorMatrix_operator]
  abel

/-- The same native chart reproduces every actually queried correction
operator. Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalDataOfOperators_correction (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric)
    (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric) (i : ℕ) (hi : i<k+1) :
    rfcPhysicalCorrection base (rfcPhysicalDataOfOperators base hQ A B hA hB) i=B i := by
  have hi' : i<k+2 := by omega
  simp only [rfcPhysicalCorrection,rfcPhysicalDataOfOperators,matrixSequenceExtension,dite_eq_left hi',
    dite_eq_left hi,cgOperator,map_add]
  change cgOperator base+cgOperator (physicalOperatorMatrix (B i-cgOperator base))=B i
  rw [physicalOperatorMatrix_operator]
  abel

/-- The exact native physical source chart has the same actual uniform
operator allowance, with no dimension factor. Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalDataOfOperators_norm (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric)
    (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric)
    (R : ℝ) (hR : 0≤R) (hAb : ∀ j<k+1, ‖A j-cgOperator base‖≤R)
    (hBb : ∀ j<k+1, ‖B j-cgOperator base‖≤R) :
    ‖rfcPhysicalDataOfOperators base hQ A B hA hB‖≤R := by
  change max ‖(fun j : Fin (k+1)=>physicalOperatorMatrix (A j.val-cgOperator base))‖
    ‖(fun j : Fin (k+2)=>if h : j.val<k+1 then physicalOperatorMatrix (B j.val-cgOperator base) else 0)‖≤R
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    rw [physicalOperatorMatrix_norm]
    exact hAb j.val j.isLt
  · apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    split_ifs with hj
    · rw [physicalOperatorMatrix_norm]
      exact hBb j.val hj
    · simpa only [norm_zero] using hR

set_option maxHeartbeats 600000 in
/-- The true frozen quadratic coefficient reads exactly the executed physical
operator prefix, including the real first secant.
Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalQuadratic_congr_prefix (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B A' B' : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j≤k, A j=A' j) (hB : B k=B' k) :
    rfcPhysicalQuadratic base g A B=rfcPhysicalQuadratic base g A' B' := by
  let U := referenceModelBasis base g k
  have hL : (Matrix.of fun i j : Fin (k+1)=>inner ℝ (U i) ((B k-A (k-(min i j).val)) (U j)))=
      (Matrix.of fun i j : Fin (k+1)=>inner ℝ (U i) ((B' k-A' (k-(min i j).val)) (U j))) := by
    ext i j
    simp only [Matrix.of_apply,hB,hA _ (Nat.sub_le _ _)]
  have hf : frozenIncoming (cgOperator base) g A k=frozenIncoming (cgOperator base) g A' k := by
    unfold frozenIncoming
    congr 1
    funext i
    refine Fin.cases rfl (fun j=>?_) i
    simp only [Fin.cons_succ,hA k le_rfl]
    rw [hA _ (by omega)]
  dsimp only [rfcPhysicalQuadratic]
  rw [hf]
  change cgOperator ((fullBasisMatrix U)ᵀ⁻¹*((Matrix.of fun i j : Fin (k+1)=>
    inner ℝ (U i) ((B k-A (k-(min i j).val)) (U j)))*_)) _=_
  rw [hL]

end
end krylov.Functions

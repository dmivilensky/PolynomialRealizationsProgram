import krylov.Functions.NativeRFCPhysicalTransfer
import krylov.Functions.RFCBilinear

/-!
Article: main_krylov, thm:Htransfer, exact finite physical tensor-jet coordinates.
Use: retain genuine source norms when replacing actual symmetric query
operators by the true third-derivative slices. Source: exact operator/matrix
linearity, the finite symmetric chart and the actual bounded bilinear response.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {k n : ℕ}

/-- The actual Euclidean operator matrix preserves subtraction.
Article: main_krylov, thm:Htransfer. -/
theorem physicalOperatorMatrix_sub (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    physicalOperatorMatrix (A-B)=physicalOperatorMatrix A-physicalOperatorMatrix B := by
  exact map_sub (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm A B

/-- The actual Euclidean operator matrix preserves real scaling.
Article: main_krylov, thm:Htransfer. -/
theorem physicalOperatorMatrix_smul (c : ℝ) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    physicalOperatorMatrix (c • A)=c • physicalOperatorMatrix A := by
  exact map_smul (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm c A

/-- Actual physical first-jet remainders pass to the full genuine symmetric
finite chart with exactly their original bound.
Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalDataOfOperators_jet_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (A B A' B' : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric) (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric)
    (hA' : ∀ j<k+1, (A' j).toLinearMap.IsSymmetric) (hB' : ∀ j<k+1, (B' j).toLinearMap.IsSymmetric)
    (c R : ℝ) (hR : 0≤R)
    (hAb : ∀ j<k+1, ‖(A j-cgOperator base)-c • (A' j-cgOperator base)‖≤R)
    (hBb : ∀ j<k+1, ‖(B j-cgOperator base)-c • (B' j-cgOperator base)‖≤R) :
    ‖rfcPhysicalDataOfOperators base hQ A B hA hB-
      c • rfcPhysicalDataOfOperators base hQ A' B' hA' hB'‖≤R := by
  classical
  change max ‖(fun j : Fin (k+1)=>physicalOperatorMatrix (A j.val-cgOperator base)-
      c • physicalOperatorMatrix (A' j.val-cgOperator base))‖
    ‖(fun j : Fin (k+2)=>(if h : j.val<k+1 then physicalOperatorMatrix (B j.val-cgOperator base) else 0)-
      c • (if h : j.val<k+1 then physicalOperatorMatrix (B' j.val-cgOperator base) else 0))‖≤R
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    rw [←physicalOperatorMatrix_smul,←physicalOperatorMatrix_sub,physicalOperatorMatrix_norm]
    exact hAb j.val j.isLt
  · apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    by_cases hj : j.val<k+1
    · simp only [dite_eq_left hj]
      rw [←physicalOperatorMatrix_smul,←physicalOperatorMatrix_sub,physicalOperatorMatrix_norm]
      exact hBb j.val hj
    · simpa only [dite_eq_right hj,smul_zero,sub_self,norm_zero] using hR

/-- The genuine physical quadratic response has exact degree two in its true
finite symmetric source, with its reference gradient fixed.
Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalQuadratic_source_smul (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1))) (Θ : RFCPhysicalData k) (c : ℝ) :
    rfcPhysicalQuadratic base g (rfcPhysicalSearch base (c • Θ)) (rfcPhysicalCorrection base (c • Θ))=
      c^2 • rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) := by
  rw [←rfcPhysicalBilinear_diagonal,←rfcPhysicalBilinear_diagonal]
  rw [map_smul,map_smul]
  change c • (c • rfcPhysicalBilinear base g Θ Θ)=c^2 • rfcPhysicalBilinear base g Θ Θ
  rw [smul_smul]
  congr 1
  ring

/-- One real first-jet estimate and a genuine source bound control the true
leading coefficient, uniformly in the reference parameter.
Article: main_krylov, thm:Htransfer. -/
theorem leading_norm_bound_of_jet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a w : V) (ε D : ℝ) (hε : 0<ε) (ha : ‖a‖≤D*ε) (hw : ‖a-ε • w‖≤ε) : ‖w‖≤D+1 := by
  have hh := norm_sub_le a (a-ε • w)
  rw [sub_sub_cancel,norm_smul,Real.norm_of_nonneg hε.le] at hh
  nlinarith only [hh,ha,hw,hε]

/-- Genuine first jets enter the actual physical quadratic response with one
additional small source factor. Article: main_krylov, thm:Htransfer.
This is the quantitative bridge for both little-o cubic and Lipschitz-third
fourth-order native cycle remainders. -/
theorem rfcPhysicalQuadratic_jet_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B A' B' : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric) (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric)
    (hA' : ∀ j<k+1, (A' j).toLinearMap.IsSymmetric) (hB' : ∀ j<k+1, (B' j).toLinearMap.IsSymmetric)
    (ε D W J M : ℝ) (hε : 0<ε) (hD : 0≤D) (hW : 0≤W) (hJ : 0≤J) (hM : 0≤M)
    (hAb : ∀ j<k+1, ‖A j-cgOperator base‖≤D*ε)
    (hBb : ∀ j<k+1, ‖B j-cgOperator base‖≤D*ε)
    (hAw : ∀ j<k+1, ‖A' j-cgOperator base‖≤W)
    (hBw : ∀ j<k+1, ‖B' j-cgOperator base‖≤W)
    (hAj : ∀ j<k+1, ‖(A j-cgOperator base)-ε • (A' j-cgOperator base)‖≤J)
    (hBj : ∀ j<k+1, ‖(B j-cgOperator base)-ε • (B' j-cgOperator base)‖≤J)
    (hresponse : ∀ Θ Ξ : RFCPhysicalData k,
      ‖rfcPhysicalQuadratic base g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)-
        rfcPhysicalQuadratic base g (rfcPhysicalSearch base Ξ) (rfcPhysicalCorrection base Ξ)‖≤
        M*(‖Θ‖+‖Ξ‖)*‖Θ-Ξ‖) :
    ‖rfcPhysicalQuadratic base g A B-ε^2 • rfcPhysicalQuadratic base g A' B'‖≤M*(D+W)*ε*J := by
  let Θ := rfcPhysicalDataOfOperators base hQ A B hA hB
  let Ω := rfcPhysicalDataOfOperators base hQ A' B' hA' hB'
  have hΘ := rfcPhysicalDataOfOperators_norm base hQ A B hA hB (D*ε) (by positivity) hAb hBb
  have hΩ := rfcPhysicalDataOfOperators_norm base hQ A' B' hA' hB' W hW hAw hBw
  have hdiff := rfcPhysicalDataOfOperators_jet_norm base hQ A B A' B' hA hB hA' hB' ε J hJ hAj hBj
  have hc (X Y : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
      (hX : ∀ j<k+1, (X j).toLinearMap.IsSymmetric) (hY : ∀ j<k+1, (Y j).toLinearMap.IsSymmetric) :
      rfcPhysicalQuadratic base g (rfcPhysicalSearch base (rfcPhysicalDataOfOperators base hQ X Y hX hY))
        (rfcPhysicalCorrection base (rfcPhysicalDataOfOperators base hQ X Y hX hY))=rfcPhysicalQuadratic base g X Y := by
    exact rfcPhysicalQuadratic_congr_prefix base g _ _ X Y
      (fun j hj=>rfcPhysicalDataOfOperators_search base hQ X Y hX hY j (by omega))
      (rfcPhysicalDataOfOperators_correction base hQ X Y hX hY k (by omega))
  have hh := hresponse Θ (ε • Ω)
  rw [rfcPhysicalQuadratic_source_smul,hc A B hA hB,hc A' B' hA' hB'] at hh
  have hnorm : ‖ε • Ω‖≤ε*W := by
    rw [norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hΩ hε.le
  exact hh.trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left (add_le_add hΘ hnorm) hM) hdiff (norm_nonneg _) (by positivity)).trans_eq (by ring))

end
end krylov.Functions

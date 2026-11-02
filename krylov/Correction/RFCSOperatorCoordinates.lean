import krylov.Correction.RFCSOperatorTube
import krylov.Methods.RFCSHomogeneous

/-!
Article: main_krylov, thm:RFCS, exact finite physical operator dictionary.
Use: Pack actual nonlinear probe and full-step representatives into the
original direct operator coordinates, with their uniform norm bound and
complete measured-prefix equality proved from the real operator actions.
Source: genuine finite RFC-S execution and the exact probe/segment difference.
-/

namespace krylov.Correction
noncomputable section
open krylov.Methods krylov.Reference
variable {k : ℕ}

/-- The original finite direct-source coordinates of actual probe and physical segment operators.
Use: Include every physical segment drift and the true probe mismatch in one genuine source profile.
Article: main_krylov, thm:RFCS, genuine finite-source operator coordinates.
-/
def rfcsParametersOfOperators (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (Ap A : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) :
    RFCSOperatorParameters (k+1) :=
  (fun i => A i.val-cgOperator base,fun i => A i.val-Ap i.val)

/-- Uniform closeness of genuine probe and full-step operators bounds their actual finite direct-source profile by twice that perturbation.
Use: Apply the compact source tubes to operators chosen from actual nonlinear queries.
Article: main_krylov, thm:RFCS, genuine finite-source operator coordinates.
Proof: Use the finite product sup norm and the triangle inequality for the true segment-minus-probe mismatch.
-/
theorem rfcsParametersOfOperators_norm_le (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (Ap A : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {η : ℝ} (hη : 0≤η) (hp : ∀ i<k+1, ‖Ap i-cgOperator base‖≤η)
    (ha : ∀ i<k+1, ‖A i-cgOperator base‖≤η) :
    ‖rfcsParametersOfOperators base Ap A‖≤2*η := by
  rw [norm_prod_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    exact (ha i.val i.isLt).trans (by linarith)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖A i.val-Ap i.val‖≤2*η
    calc
      _ = ‖(A i.val-cgOperator base)-(Ap i.val-cgOperator base)‖ := by congr 1; abel
      _ ≤ ‖A i.val-cgOperator base‖+‖Ap i.val-cgOperator base‖ := norm_sub_le _ _
      _ ≤ 2*η := by linarith [ha i.val i.isLt,hp i.val i.isLt]

/-- The finite direct-source profile exactly reproduces the entire genuine operator history through the original cycle horizon.
Use: Identify actual nonlinear measured transcripts with the source on which the compact operator estimates were proved.
Article: main_krylov, thm:RFCS, genuine finite-source operator coordinates.
Proof: Every genuine physical and probe operator agrees at all requested indices; apply complete finite-prefix execution congruence.
-/
theorem rfcsParametersOfOperators_realizes (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (Ap A : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) (N : ℕ) (hN : N≤k+1) :
    rfcSRun fullMemory Ap A A g N=
      rfcSRun fullMemory (rfcsDirectProbe base (g,rfcsParametersOfOperators base Ap A))
        (rfcsDirectLine base (g,rfcsParametersOfOperators base Ap A))
        (rfcsDirectLine base (g,rfcsParametersOfOperators base Ap A)) g N := by
  have ha i (hi : i<N) : rfcsDirectLine base (g,rfcsParametersOfOperators base Ap A) i=A i := by
    simp only [rfcsDirectLine,rfcsOperatorAt,dite_eq_left (hi.trans_le hN),rfcsParametersOfOperators,
      add_sub_cancel]
  apply rfcSRun_congr_prefix
  · intro i hi
    rw [rfcsDirectProbe,ha i hi]
    simp only [rfcsOperatorAt,dite_eq_left (hi.trans_le hN),rfcsParametersOfOperators,
      sub_sub_cancel]
  · intro i hi
    exact (ha i hi).symm
  · intro i hi
    exact (ha i hi).symm

end
end krylov.Correction

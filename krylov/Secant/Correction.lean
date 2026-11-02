import krylov.Secant.Canonical
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

/-!
Article: main_krylov, Appendix A, apA:galerkin(a), correction and anchor identities.
Use: exact algebra for arbitrary rectangular windows precedes all perturbative
estimates. Invertibility is proved or supplied explicitly before using an inverse.
Source: matrix associativity and the nonsingular-inverse API in mathlib.
-/

namespace krylov.Secant
noncomputable section
open Matrix
open scoped Matrix
variable {n p : ℕ}

/-- The actual gradient after taking a correction in the stored window.
Use: models an independently queried correction segment with operator B.
Article: main_krylov, def:model(a) and apA:galerkin(a). -/
def correctedGradient (U : Matrix (Fin n) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) (w : Fin p → ℝ) : Fin n → ℝ :=
  g + B *ᵥ (U *ᵥ w)

/-- The coefficient vector from the actual nonsingular model solve.
Use: every latest-information correction uses this coefficient vector.
Article: main_krylov, apA:galerkin(a), w = −H⁻¹Uᵀg. -/
def correctionCoefficients (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (g : Fin n → ℝ) : Fin p → ℝ :=
  -(H⁻¹ *ᵥ (Uᵀ *ᵥ g))

/-- A nonsingular model inverse solves the correction equation exactly.
Use: removes the model-solve premise for the concrete correction coefficients.
Article: main_krylov, apA:galerkin(a).
Proof: cancel the right nonsingular inverse before acting on the residual. -/
theorem correctionCoefficients_solve (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (hH : IsUnit H.det) (g : Fin n → ℝ) :
    H *ᵥ correctionCoefficients U H g = -(Uᵀ *ᵥ g) := by
  rw [correctionCoefficients, mulVec_neg, mulVec_mulVec, mul_nonsing_inv H hH, one_mulVec]

/-- The projected corrected gradient is exactly the model-error action.
Use: applies also to dependent windows, provided the stated solve is available.
Article: main_krylov, apA:galerkin(a), first correction identity.
Proof: distribute the projection and substitute the correction equation. -/
theorem projected_correction (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (g : Fin n → ℝ) (w : Fin p → ℝ) (hw : H *ᵥ w = -(Uᵀ *ᵥ g)) :
    Uᵀ *ᵥ correctedGradient U B g w = (Uᵀ * B * U - H) *ᵥ w := by
  simp only [correctedGradient, mulVec_add, sub_mulVec, ← mulVec_mulVec, hw]
  abel

/-- A fixed model correction propagates its projected residual by the error matrix.
Use: the exact recurrence for any finite number of corrections.
Article: main_krylov, apA:galerkin(a), r_(p+1) = −(UᵀBU−H)H⁻¹r_p.
Proof: apply the solved projected identity and associate the inverse action. -/
theorem projected_correction_inverse (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (hH : IsUnit H.det)
    (B : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    Uᵀ *ᵥ correctedGradient U B g (correctionCoefficients U H g) =
      -((Uᵀ * B * U - H) * H⁻¹) *ᵥ (Uᵀ *ᵥ g) := by
  rw [projected_correction U H B g _ (correctionCoefficients_solve U H hH g)]
  simp only [correctionCoefficients, neg_mulVec, mulVec_neg, ← mulVec_mulVec]

/-- A predicted line gradient and actual line gradient differ by the probe mismatch.
Use: corrections remain exact when prediction, secant and correction operators differ.
Article: main_krylov, apA:galerkin(a), eq:predicted-correction.
Proof: add the probe mismatch to the solved predicted residual. -/
theorem predicted_correction (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (Ap As B : Matrix (Fin n) (Fin n) ℝ)
    (g d : Fin n → ℝ) (w : Fin p → ℝ) (α : ℝ)
    (hw : H *ᵥ w = -(Uᵀ *ᵥ (g + α • (Ap *ᵥ d)))) :
    Uᵀ *ᵥ correctedGradient U B (g + α • (As *ᵥ d)) w =
      α • ((Uᵀ * (As - Ap)) *ᵥ d) + (Uᵀ * B * U - H) *ᵥ w := by
  -- Expand the two actual segment actions, retaining their difference explicitly.
  simp only [mulVec_add, mulVec_smul] at hw
  simp only [correctedGradient, mulVec_add, mulVec_smul, sub_mulVec,
    ← mulVec_mulVec, mulVec_sub, hw, smul_sub]
  abel

/-- A model column matching the new probe makes the corrected point anchor-independent.
Use: changing the exact line length does not change the full model correction.
Article: main_krylov, apA:galerkin(a), final anchor identity.
Proof: recover the last coordinate through the inverse model and cancel the line step. -/
theorem correction_anchor (U : Matrix (Fin n) (Fin p) ℝ)
    (H : Matrix (Fin p) (Fin p) ℝ) (hH : IsUnit H.det)
    (g z d : Fin n → ℝ) (e : Fin p → ℝ)
    (hd : U *ᵥ e = d) (hz : H *ᵥ e = Uᵀ *ᵥ z) (α : ℝ) :
    α • d - U *ᵥ (H⁻¹ *ᵥ (Uᵀ *ᵥ (g + α • z))) =
      -(U *ᵥ (H⁻¹ *ᵥ (Uᵀ *ᵥ g))) := by
  have he : H⁻¹ *ᵥ (Uᵀ *ᵥ z) = e := by
    rw [← hz, mulVec_mulVec, nonsing_inv_mul H hH, one_mulVec]
  simp only [mulVec_add, mulVec_smul, he, hd]
  abel

/-- A square window correction is exactly the inverse ambient model step.
Use: connects coefficient solves to the physical model J=U⁻ᵀHU⁻¹.
Article: main_krylov, apA:galerkin(a), Uw=−J⁻¹g.
Proof: use the exact inverse congruence and associate its vector action. -/
theorem square_correction_step (U H : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsUnit U.det) (g : Fin n → ℝ) :
    U *ᵥ correctionCoefficients U H g = -(inverseCongruence U H)⁻¹ *ᵥ g := by
  rw [inverseCongruence_inv U H hU]
  simp only [correctionCoefficients, mulVec_neg, neg_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- The actual corrected gradient is exactly the ambient model-error action.
Use: a square correction removes the entire modeled physical curvature.
Article: main_krylov, apA:galerkin(a), g₊=(B−J)Uw.
Proof: the model solve gives JUw=−g; subtract this from the true operator action. -/
theorem square_corrected_gradient (U H B : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsUnit U.det) (hH : IsUnit H.det) (g : Fin n → ℝ) :
    correctedGradient U B g (correctionCoefficients U H g) =
      (B - inverseCongruence U H) *ᵥ (U *ᵥ correctionCoefficients U H g) := by
  have ht : IsUnit Uᵀ.det := by simpa only [det_transpose] using hU
  have hs : inverseCongruence U H *ᵥ (U *ᵥ correctionCoefficients U H g) = -g := by
    -- Cancel coordinates before substituting the solved finite-dimensional model equation.
    rw [inverseCongruence, ← mulVec_mulVec, mulVec_mulVec _ U⁻¹ U,
      nonsing_inv_mul _ hU, one_mulVec, ← mulVec_mulVec, correctionCoefficients_solve U H hH g,
      mulVec_neg, mulVec_mulVec, nonsing_inv_mul _ ht, one_mulVec]
  rw [sub_mulVec, hs, sub_neg_eq_add, correctedGradient, add_comm]

/-- The actual square-window correction satisfies the exact canonical normal equation.
Use: the first-order and repeated-correction estimates start from the real physical solve.
Article: main_krylov, apA:galerkin(a), eq:correction-normal.
Proof: replace the physical correction by its inverse ambient model action;
the two metric-root cancellations give the same canonical operator product. -/
theorem canonical_corrected_gradient (U H B base : Matrix (Fin n) (Fin n) ℝ)
    (hU : IsUnit U.det) (hH : IsUnit H.det) (hbase : base.PosDef) (g : Fin n → ℝ) :
    (metricRoot base)⁻¹ *ᵥ correctedGradient U B g (correctionCoefficients U H g) =
      -(relativeOperator base (B - inverseCongruence U H) *
        (relativeOperator base (inverseCongruence U H))⁻¹) *ᵥ ((metricRoot base)⁻¹ *ᵥ g) := by
  have he : relativeOperator base (B - inverseCongruence U H) *
      (relativeOperator base (inverseCongruence U H))⁻¹ * (metricRoot base)⁻¹ =
      (metricRoot base)⁻¹ * (B - inverseCongruence U H) * (inverseCongruence U H)⁻¹ := by
    rw [relativeOperator_inv base _ hbase]
    unfold relativeOperator
    calc
      _ = (metricRoot base)⁻¹ * (B - inverseCongruence U H) *
          ((metricRoot base)⁻¹ * metricRoot base) * (inverseCongruence U H)⁻¹ *
          (metricRoot base * (metricRoot base)⁻¹) := by noncomm_ring
      _ = _ := by rw [nonsing_inv_mul _ (metricRoot_det_unit base hbase),
        mul_nonsing_inv _ (metricRoot_det_unit base hbase)]; simp
  -- Substitute the solved physical correction before applying the coordinate product identity.
  rw [square_corrected_gradient U H B hU hH g, square_correction_step U H hU g]
  simp only [neg_mulVec, mulVec_neg, mulVec_mulVec, Matrix.neg_mul]
  rw [he, Matrix.mul_assoc]

end
end krylov.Secant

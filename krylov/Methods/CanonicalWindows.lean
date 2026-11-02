import krylov.Methods.WindowCoordinates
import krylov.Reference.CanonicalGradient

/-!
Article: main_krylov, lem:projected-residual, actual physical/canonical rectangular windows.
Use: the genuine positive metric root preserves observed pairings and actual
model coefficients, while its primal action maps the true physical correction.
Source: the proved canonical search pairing and actual finite physical synthesis.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.Secant
open scoped InnerProductSpace
variable {n p : ℕ}

/-- The actual primal metric-root coordinates of a rectangular physical window.
Use: physical step columns become the source's true canonical step columns.
Article: main_krylov, lem:projected-residual, A^(1/2)U. -/
def primalWindow (base : Matrix (Fin n) (Fin n) ℝ) (s : Fin p → EuclideanSpace ℝ (Fin n)) :
    Fin p → EuclideanSpace ℝ (Fin n) := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s i)

/-- The actual dual inverse-root coordinates of rectangular observed gradient images.
Use: secants and gradients transform dually to actual physical displacements.
Article: main_krylov, lem:projected-residual, A^(−1/2)Y. -/
def dualWindow (base : Matrix (Fin n) (Fin n) ℝ) (y : Fin p → EuclideanSpace ℝ (Fin n)) :
    Fin p → EuclideanSpace ℝ (Fin n) := fun i => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (y i)

/-- The actual inverse-root map cancels the genuine primal metric-root map.
Use: canonical rectangular operator actions represent the true physical segment actions.
Article: main_krylov, lem:projected-residual, actual metric cancellation.
Proof: multiply the true nonsingular positive root inverse by its actual root before acting on the vector. -/
theorem canonical_primal_dual_cancel (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) v)=v := by
  rw [← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]

/-- A genuine physical segment operator in its actual canonical primal/dual coordinates.
Use: actual correction gradients transform through the same operator used in the canonical residual bounds.
Article: main_krylov, lem:projected-residual, B̂=A^(−1/2)BA^(−1/2). -/
def canonicalOperator (base : Matrix (Fin n) (Fin n) ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹).comp
    (B.comp (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹))

/-- The true canonical operator action on a primal physical step is exactly the dual image of the actual physical action.
Use: the canonical residual recurrence analyzes the actual independently queried correction segment.
Article: main_krylov, lem:projected-residual, physical/canonical oracle bridge.
Proof: unfold the actual composed operator and cancel the real inverse-root/root pair on the genuine step. -/
theorem canonicalOperator_primal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    canonicalOperator base B (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) v)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (B v) := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (B (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) v)))=_
  rw [canonical_primal_dual_cancel base hb]

/-- Every actual physical correction-gradient update has the genuine canonical update with its true primal step.
Use: all canonical one-step residual estimates refer to the real physical observation.
Article: main_krylov, lem:projected-residual, actual canonical gradient update.
Proof: the inverse-root map is linear and the proved canonical operator identity identifies its true segment action. -/
theorem canonical_gradient_update (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (g v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (g+B v)=
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g+
        canonicalOperator base B (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) v) := by
  rw [map_add,canonicalOperator_primal base hb]

/-- The actual exact-search scalar is unchanged in genuine canonical primal/dual coordinates.
Use: the source's canonical search is the real physical search without an assumed step-length replacement.
Article: main_krylov, lem:projected-residual, exact line search in canonical coordinates.
Proof: both real numerator and real curvature are exactly the proved preserved search pairings. -/
theorem canonical_lineLength (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g d z : EuclideanSpace ℝ (Fin n)) :
    lineLength (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) d)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ z)=lineLength g d z := by
  rw [lineLength,lineLength,← canonical_search_pairing base hb,← canonical_search_pairing base hb]

/-- Actual rectangular physical projected coordinates equal their genuine primal/dual canonical coordinates.
Use: no gradient pairing or model right-hand side is assumed invariant without proof.
Article: main_krylov, lem:projected-residual, physical/canonical projection bridge.
Proof: apply the proved true canonical search pairing to each actual physical column. -/
theorem canonical_window_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n)) :
    coordinates (primalWindow base s) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)=coordinates s g := by
  ext i
  exact (canonical_search_pairing base hb (s i) g).symm

/-- The actual newest-information model of a rectangular window is unchanged in genuine canonical coordinates.
Use: the canonical projected-residual theorem applies to the true physical coefficient model.
Article: main_krylov, lem:projected-residual, same H before column-length normalization.
Proof: the actual newer-pair inner product is precisely the preserved primal/dual search pairing. -/
theorem canonical_pairModel (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : Fin p → EuclideanSpace ℝ (Fin n)) :
    pairModel (primalWindow base s) (dualWindow base y)=pairModel s y := by
  ext i j
  exact (canonical_search_pairing base hb (s (max i j)) (y (min i j))).symm

/-- The genuine canonical model correction is exactly the metric-root image of the actual physical correction.
Use: normalized canonical movement estimates bound the true executed rectangular-window solve.
Article: main_krylov, lem:projected-residual, physical χ and canonical A^(1/2)χ.
Proof: the actual coefficient right-hand side is preserved by the genuine
primal/dual pairing, and the true root commutes with the actual finite physical synthesis. -/
theorem canonical_modelCorrection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (H : Matrix (Fin p) (Fin p) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) :
    combine (primalWindow base s) (modelCoefficients (primalWindow base s) H
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g))=
        Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (combine s (modelCoefficients s H g)) := by
  have hc : modelCoefficients (primalWindow base s) H
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)=modelCoefficients s H g := by
    rw [modelCoefficients,canonical_window_coordinates base hb]
    rfl
  rw [hc]
  exact (combine_operator _ s _).symm

end
end krylov.Methods

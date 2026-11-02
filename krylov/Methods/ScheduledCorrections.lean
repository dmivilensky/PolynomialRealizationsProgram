import krylov.Methods.CorrectionPairs
import krylov.Methods.ProjectedCorrectionOrder

/-!
Article: main_krylov, def:classes(M) and apD:eq:pairs, independently queried correction segments.
Use: permit a different actual segment operator for each observed correction;
constant schedules recover the existing policy execution exactly.
Source: finite nonanticipating oracle execution and exact additive telescoping.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Execute the actual finite correction tree with a separately prescribed operator at each query.
Use: independent correction probes reveal only their actual returned gradients.
Article: main_krylov, def:classes(M), correction operators B_i^(p). -/
def runScheduledCorrections (q : CorrectionTree E) (B : ℕ → E →L[ℝ] E)
    (offset : ℕ) (g : E) : CorrectionResult E :=
  match q with
  | .done => ⟨0,g,[]⟩
  | .query u next =>
    let gnew := g+B offset u
    let r := runScheduledCorrections (next gnew) B (offset+1) gnew
    ⟨u+r.movement,r.gradient,(u,gnew)::r.trace⟩

/-- A constant real correction-operator schedule recovers the original actual executor exactly.
Use: every existing RFC result remains an instance of the independent-segment protocol.
Article: main_krylov, def:classes(M) and lem:projected-residual.
Proof: both executions return the same observed gradient at every query and select the same continuation. -/
theorem runScheduledCorrections_const (q : CorrectionTree E) (B : E →L[ℝ] E) (offset : ℕ) (g : E) :
    runScheduledCorrections q (fun _ => B) offset g=runCorrections q B g := by
  induction q generalizing offset g with
  | done => rfl
  | query u next ih =>
    simp only [runScheduledCorrections, runCorrections]
    rw [ih]

/-- Sum the mismatches of the actually recorded correction displacements against the line operator.
Use: each summand uses its actual query index and its actual observed trace entry.
Article: main_krylov, apD:eq:pairs, Σ_p(B_i^(p)−A_i)χ_i^(p). -/
def correctionMismatchSum (A : E →L[ℝ] E) (B : ℕ → E →L[ℝ] E) :
    ℕ → List (E × E) → E
  | _, [] => 0
  | offset, pair::trace => (B offset-A) pair.1+correctionMismatchSum A B (offset+1) trace

/-- Independently queried real correction segments give exactly the source's complete recorded-pair defect sum.
Use: covers arbitrary finite adaptive correction trees and all independently varying correction operators.
Article: main_krylov, apD:eq:pairs.
Proof: the real new gradient selects each real next subtree; its balance
telescopes after adding the line image and the actual query-indexed mismatch. -/
theorem scheduled_correction_pair_identity (q : CorrectionTree E) (A : E →L[ℝ] E)
    (B : ℕ → E →L[ℝ] E) (offset : ℕ) (g : E) :
    (runScheduledCorrections q B offset g).gradient=
      g+A (runScheduledCorrections q B offset g).movement+
        correctionMismatchSum A B offset (runScheduledCorrections q B offset g).trace := by
  -- The oracle index advances only after an actual correction query, including zero displacements.
  induction q generalizing offset g with
  | done => simp only [runScheduledCorrections, correctionMismatchSum, map_zero, add_zero]
  | query u next ih =>
    change (runScheduledCorrections (next (g+B offset u)) B (offset+1) (g+B offset u)).gradient=_
    rw [ih]
    change (g+B offset u)+A _+correctionMismatchSum A B (offset+1) _=
      g+A (u+_)+((B offset-A) u+correctionMismatchSum A B (offset+1) _)
    rw [map_add, _root_.sub_apply]
    abel

variable {p : ℕ}

/-- Every independently queried repeated RFC correction satisfies the same normalized finite-query bound.
Use: the printed correction order is valid when the correction operator changes between queries.
Article: main_krylov, lem:projected-residual, repeated fixed-model corrections.
Proof: induction follows the actual returned gradient and uses the common
normalized error and inverse bound for the real next scheduled operator. -/
theorem scheduled_model_projected_bound (s : Fin p → E) (H : Matrix (Fin p) (Fin p) ℝ)
    (d : Fin p → ℝ) (hd : IsUnit (diagonal d).det) (hH : IsUnit (rescaleModel H d).det)
    (B : ℕ → E →L[ℝ] E) (offset c : ℕ) (g : E) {M : ℝ} (hM : 0≤M)
    (hB : ∀ j<c, ‖correctionCompression (rescaleWindow s d) (B (offset+j))-rescaleModel H d‖*
      ‖(rescaleModel H d)⁻¹‖≤M) :
    ‖projectedResidual (rescaleWindow s d)
      (runScheduledCorrections (repeatedModelTree s H c g) B offset g).gradient‖≤
        M^c*‖projectedResidual (rescaleWindow s d) g‖ := by
  -- Each induction step uses the actual next correction gradient and advances its real oracle index.
  induction c generalizing offset g with
  | zero => simp only [repeatedModelTree, runScheduledCorrections, pow_zero, one_mul, le_refl]
  | succ c ih =>
    change ‖projectedResidual (rescaleWindow s d)
      (runScheduledCorrections (repeatedModelTree s H c _) B (offset+1) _).gradient‖≤_
    have ht := ih (offset+1) (g+B offset (combine s (modelCoefficients s H g))) (fun j hj => by
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hB (j+1) (by omega))
    have hstep := (normalizedCorrection_bound s H d hd hH (B offset) g).trans
      (mul_le_mul_of_nonneg_right (by simpa only [Nat.add_zero] using hB 0 (by omega)) (norm_nonneg _))
    exact (ht.trans (mul_le_mul_of_nonneg_left hstep (pow_nonneg hM c))).trans_eq
      (by rw [pow_succ]; ring)

end
end krylov.Methods

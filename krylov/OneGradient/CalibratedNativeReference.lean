import krylov.OneGradient.InformedNativeCalibration
import krylov.OneGradient.CalibratedDirectionError
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), general calibrated observed trials.
Use: derive actual native reference data for arbitrary history-only rules
whose true quadratic trials equal CG lengths; no calibrated form is assumed.
Source: complete quadratic S/D history equivalence, actual full-memory CG
consistency and real observed trial calibration.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Primitive reference calibration of a real history-only trial rule.
Use: the general known-base expansion assumes actual exact quadratic
trials, rather than a supplied trajectory or an incoming/output jet.
Article: main_krylov, thm:local(a), general calibrated policy. -/
def CalibratedTrial (trial : History E → ℝ) (Q : E →L[ℝ] E) (g : E) (N : ℕ) : Prop :=
  ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)=CG.length Q g i

/-- Genuine exact quadratic trial calibration implies actual nonzero
reference trials in both native bases, with their true CG lengths.
Use: the real basis equivalence and replay domains are derived.
Article: main_krylov, thm:local(a), general true native trial calibration.
Proof: active positive CG geometry makes every calibrated S trial nonzero.
The proved complete quadratic S/D histories coincide, so the same actual
history-only decision is the true CG length in either native basis. -/
theorem calibrated_native_reference_trial (directions : Bool) (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (Q : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : (EuclideanSpace ℝ (Fin n)),v≠0 → 0 < inner ℝ v (Q v)) (g : (EuclideanSpace ℝ (Fin n))) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k<N) :
    trial (oneGradientRun (xrfcBasisMethod directions trial) (fun _ => Q) g k)=CG.length Q g k := by
  have ht (i : ℕ) (hi : i<N) : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0 := by
    rw [hcal i hi]
    exact (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hpre j (hj.trans hi))) (hpre i hi)).2.1.ne'
  cases directions with
  | false => exact hcal k hk
  | true =>
    change trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k)=_
    rw [xrfc_quadratic_basis_histories trial Q hQ hpos g N hpre ht k hk.le]
    exact hcal k hk

/-- Every actual calibrated S evaluated point is the true CG point.
Use: the actual incoming reference gradient is derived before any row jet.
Article: main_krylov, thm:local(a), general true evaluated reference.
Proof: the full-memory actual evaluated-point identity uses its true
selected length, which calibration identifies with the genuine CG length. -/
theorem calibrated_reference_evaluated (trial : History E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (hcal : CalibratedTrial trial Q g N)
    (k : ℕ) (hk : k≤N) :
    (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g k).displacement=CG.displacement Q g k := by
  cases k with
  | zero => rfl
  | succ k =>
    have ht (i : ℕ) (hi : i<N) : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => Q) g i)≠0 := by
      rw [hcal i hi]
      exact (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i (fun j hj => hpre j (hj.trans hi))) (hpre i hi)).2.1.ne'
    have h := xrfc_full_evaluated trial Q hQ hpos g N hpre ht k (by omega)
    dsimp only at h
    rw [hcal k (by omega)] at h
    exact h.trans (CG.displacement_succ Q g k).symm

end
end krylov.OneGradient

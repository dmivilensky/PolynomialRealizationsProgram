import polyak.ModeLocking.Continuation.LeftNormalization
import polyak.ModeLocking.Continuation.Primal

/-! Analytic square equations for the left kernel, including the literal
sum of its nonzero class masses. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open scoped BigOperators

def leftSystem {d : ℕ} (A : Parameters → Matrix (Fin d) (Fin d) ℝ) (j : Fin d)
    (mass : ℝ) (z : Parameters × (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => if i = j then (∑ r, z.2 r) - mass else (A z.1).transpose.mulVec z.2 i

theorem analyticAt_leftSystem {d : ℕ} (A : Parameters → Matrix (Fin d) (Fin d) ℝ)
    (j : Fin d) (mass : ℝ) (p : Parameters) (v : Fin d → ℝ)
    (ha : ∀ r i, AnalyticAt ℝ (fun p => A p r i) p) :
    AnalyticAt ℝ (leftSystem A j mass) (p, v) := by
  have hv (r : Fin d) : AnalyticAt ℝ (fun z : Parameters × (Fin d → ℝ) => z.2 r) (p, v) := by
    have hc : AnalyticAt ℝ (fun x : Fin d → ℝ => x r) v :=
      (ContinuousLinearMap.proj (R := ℝ) r : (Fin d → ℝ) →L[ℝ] ℝ).analyticAt v
    have hin : AnalyticAt ℝ (fun z : Parameters × (Fin d → ℝ) => z.2) (p, v) := analyticAt_snd
    exact hc.comp hin
  apply AnalyticAt.pi
  intro i
  by_cases hi : i = j
  · change AnalyticAt ℝ (fun z : Parameters × (Fin d → ℝ) =>
      if i = j then (∑ r, z.2 r) - mass else _) (p, v)
    simp only [ite_eq_left hi]
    exact (Finset.analyticAt_fun_sum Finset.univ (fun r _ => hv r)).sub analyticAt_const
  · change AnalyticAt ℝ (fun z : Parameters × (Fin d → ℝ) =>
      if i = j then _ else (A z.1).transpose.mulVec z.2 i) (p, v)
    simp only [ite_eq_right hi, Matrix.mulVec, Matrix.transpose_apply, dotProduct]
    apply Finset.analyticAt_fun_sum
    intro r _
    exact ((ha r i).comp (f := fun z : Parameters × (Fin d → ℝ) => z.1) analyticAt_fst).mul (hv r)

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem leftSystem_base {A : Continuation.Parameters → Matrix (Fin D.d) (Fin D.d) ℝ}
    (hA : A (Continuation.parameters q) = D.matrix) :
    Continuation.leftSystem A D.normalizationIndex (∑ r, D.classWeight r)
      (Continuation.parameters q, D.classWeight) = 0 := by
  funext i
  change (if i = D.normalizationIndex then _ else _) = 0
  by_cases hi : i = D.normalizationIndex
  · simp only [ite_eq_left hi, sub_self]
  · rw [ite_eq_right hi, hA, D.matrix_transpose_mul_classWeight]
    rfl

theorem hasFDerivAt_leftSystem_partial
    (A : Continuation.Parameters → Matrix (Fin D.d) (Fin D.d) ℝ)
    (hA : A (Continuation.parameters q) = D.matrix) :
    HasFDerivAt (fun v => Continuation.leftSystem A D.normalizationIndex
      (∑ r, D.classWeight r) (Continuation.parameters q, v)) D.leftNormalEquiv.toContinuousLinearMap
      D.classWeight := by
  have he : (fun v => Continuation.leftSystem A D.normalizationIndex
      (∑ r, D.classWeight r) (Continuation.parameters q, v)) =
      fun v => D.leftNormalEquiv v - fun i => if i = D.normalizationIndex then
        (∑ r, D.classWeight r) else 0 := by
    funext v i
    change (if i = D.normalizationIndex then _ else _) =
      D.leftNormalMatrix.mulVec v i - (if i = D.normalizationIndex then _ else 0)
    by_cases hi : i = D.normalizationIndex
    · simp only [ite_eq_left hi, leftNormalMatrix, Matrix.mulVec, dotProduct, one_mul]
    · simp only [ite_eq_right hi, leftNormalMatrix, Matrix.mulVec, dotProduct, sub_zero,
        Matrix.transpose_apply, hA]
  rw [he]
  exact D.leftNormalEquiv.toContinuousLinearMap.hasFDerivAt.sub_const _

end polyak.ModeLocking.RegularData

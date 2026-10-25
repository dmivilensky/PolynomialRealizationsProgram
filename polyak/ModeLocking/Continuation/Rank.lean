import polyak.ModeLocking.Continuation.Data
import Mathlib.Topology.Instances.Matrix

/-! Rank persists by the explicit normalized left-kernel system, rather
than assuming constancy of rank under perturbation. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open scoped BigOperators

def normalMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i r => if i = j then 1 else A r i

theorem rank_of_normalization {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (j : Fin d)
    (μ : Fin d → ℝ) (hμ : A.transpose.mulVec μ = 0) (hmass : (∑ r, μ r) ≠ 0)
    (hn : Function.Injective (normalMatrix A j).mulVec) : A.rank = d - 1 := by
  have hμne : μ ≠ 0 := by intro he; apply hmass; simp [he]
  have hker : A.transpose.mulVecLin.ker = Submodule.span ℝ {μ} := by
    apply le_antisymm
    · intro v hv
      let c := (∑ r, v r) / (∑ r, μ r)
      let z := v - c • μ
      have hzker : A.transpose.mulVec z = 0 := by
        simp only [z, Matrix.mulVec_sub, Matrix.mulVec_smul, show A.transpose.mulVec v = 0 from hv,
          hμ, smul_zero, sub_zero]
      have hzsum : (∑ r, z r) = 0 := by
        simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [show c * (∑ r, μ r) = ∑ r, v r from div_mul_cancel₀ _ hmass, sub_self]
      have hnz : (normalMatrix A j).mulVec z = 0 := by
        funext i
        change (∑ r, normalMatrix A j i r * z r) = 0
        by_cases hi : i = j
        · simpa only [normalMatrix, ite_eq_left hi, one_mul] using hzsum
        · have hh := congrFun hzker i
          simpa only [normalMatrix, ite_eq_right hi, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] using hh
      have hz : z = 0 := hn (hnz.trans (Matrix.mulVec_zero _).symm)
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      exact (sub_eq_zero.mp hz).symm
    · exact Submodule.span_le.mpr (by simp only [Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]; exact hμ)
  have he := A.transpose.mulVecLin.finrank_range_add_finrank_ker
  rw [hker, finrank_span_singleton hμne, Module.finrank_pi, Fintype.card_fin] at he
  have hr : A.transpose.rank + 1 = d := he
  rw [Matrix.rank_transpose] at hr
  omega

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

theorem matrix_rank : ∀ᶠ p in 𝓝 (Continuation.parameters q),
    (D.continuedMatrix C.primalShift p).rank = D.d - 1 := by
  let A := fun p => Continuation.normalMatrix (D.continuedMatrix C.primalShift p) D.normalizationIndex
  have ha : ContinuousAt A (Continuation.parameters q) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro r
    change ContinuousAt (fun p => if i = D.normalizationIndex then (1 : ℝ) else
      D.continuedMatrix C.primalShift p r i) (Continuation.parameters q)
    by_cases hi : i = D.normalizationIndex
    · simp only [ite_eq_left hi]
      exact continuousAt_const
    · simp only [ite_eq_right hi]
      exact (D.analyticAt_continuedMatrix C.primalShift C.analytic_primalShift C.primalShift_base r i).continuousAt
  have hbase : A (Continuation.parameters q) = D.leftNormalMatrix := by
    unfold A Continuation.normalMatrix
    rw [D.continuedMatrix_base C.primalShift C.primalShift_base]
    rfl
  have hnonzero : (A (Continuation.parameters q)).det ≠ 0 := by
    rw [hbase]
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det D.leftNormalMatrix).mp
      (Matrix.mulVec_injective_iff_isUnit.mp D.leftNormalMatrix_injective))
  have hdet : ∀ᶠ p in 𝓝 (Continuation.parameters q), (A p).det ≠ 0 :=
    ((continuous_id.matrix_det : Continuous (fun M : Matrix (Fin D.d) (Fin D.d) ℝ => M.det)).continuousAt.comp ha).eventually_ne hnonzero
  filter_upwards [C.equations, hdet] with p hp hnp
  apply Continuation.rank_of_normalization _ D.normalizationIndex (C.mass p) hp.2.1
  · rw [hp.2.2.2.1]
    exact D.classWeight_sum_pos.ne'
  · exact Matrix.mulVec_injective_of_det_ne_zero hnp

end polyak.ModeLocking.RegularData.ContinuationData

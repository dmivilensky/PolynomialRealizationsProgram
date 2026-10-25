import polyak.ModeLocking.Continuation.Dual

/-! Both analytic kernels, with their original normalizations and positive
components. The positive right kernel determines the remaining left-kernel
equation. -/
noncomputable section
namespace polyak.ModeLocking.Continuation
open scoped BigOperators

theorem complete_left_kernel {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (w v : Fin d → ℝ) (j : Fin d) (hw : A.mulVec w = 0) (hwj : w j ≠ 0)
    (hv : ∀ i, i ≠ j → A.transpose.mulVec v i = 0) : A.transpose.mulVec v = 0 := by
  have hs : (∑ i, w i * A.transpose.mulVec v i) = 0 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r _
    have hr := congrFun hw r
    change (∑ i, A r i * w i) = 0 at hr
    calc
      ∑ i, w i * (A r i * v r) = (∑ i, A r i * w i) * v r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hr, zero_mul]
  have hsingle : (∑ i, w i * A.transpose.mulVec v i) = w j * A.transpose.mulVec v j := by
    apply Finset.sum_eq_single j
    · intro i _ hi
      rw [hv i hi, mul_zero]
    · simp
  rw [hsingle] at hs
  have hj : A.transpose.mulVec v j = 0 := (mul_eq_zero.mp hs).resolve_left hwj
  funext i
  change A.transpose.mulVec v i = 0
  by_cases hi : i = j
  · rw [hi, hj]
  · exact hv i hi

end polyak.ModeLocking.Continuation

namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem analytic_kernel_continuation :
    ∃ (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
      (μ : Continuation.Parameters → (Fin D.d → ℝ)),
      AnalyticAt ℝ ψ (Continuation.parameters q) ∧ AnalyticAt ℝ μ (Continuation.parameters q) ∧
      ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ)) ∧
      μ (Continuation.parameters q) = D.classWeight ∧
      (∀ᶠ p in 𝓝 (Continuation.parameters q),
        (D.continuedMatrix ψ p).mulVec (ψ p).2 = 0 ∧
        (D.continuedMatrix ψ p).transpose.mulVec (μ p) = 0 ∧
        (∑ i, (ψ p).2 i) = 1 ∧ (∑ r, μ p r) = ∑ r, D.classWeight r ∧
        (∀ i, 0 < (ψ p).2 i) ∧ ∀ r, 0 < μ p r) := by
  obtain ⟨ψ, hψ, hψbase, hψsol⟩ := D.analytic_primal_continuation
  obtain ⟨μ, hμ, hμbase, hμsol⟩ := D.analytic_left_continuation ψ hψ hψbase
  refine ⟨ψ, μ, hψ, hμ, hψbase, hμbase, ?_⟩
  filter_upwards [hψsol, hμsol] with p hp hμp
  have hright := congrArg Prod.fst hp.1
  change (D.continuedMatrix ψ p).mulVec (ψ p).2 = 0 at hright
  have hnorm := congrArg Prod.snd hp.1
  change (∑ i, (ψ p).2 i) - 1 = 0 at hnorm
  have hleft (i : Fin D.d) (hi : i ≠ D.normalizationIndex) :
      (D.continuedMatrix ψ p).transpose.mulVec (μ p) i = 0 := by
    have hz := congrFun hμp.1 i
    change (if i = D.normalizationIndex then _ else _) = 0 at hz
    rw [ite_eq_right hi] at hz
    exact hz
  have hfull := Continuation.complete_left_kernel (D.continuedMatrix ψ p) (ψ p).2 (μ p)
    D.normalizationIndex hright (hp.2 _).ne' hleft
  have hμnorm := congrFun hμp.1 D.normalizationIndex
  change (if D.normalizationIndex = D.normalizationIndex then
    (∑ r, μ p r) - (∑ r, D.classWeight r) else _) = 0 at hμnorm
  simp only [ite_true] at hμnorm
  exact ⟨hright, hfull, sub_eq_zero.mp hnorm, sub_eq_zero.mp hμnorm, hp.2, hμp.2⟩

end polyak.ModeLocking.RegularData

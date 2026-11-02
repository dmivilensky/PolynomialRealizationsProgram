import krylov.Asymptotics.RecoveryConsistency
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Article: main_krylov, lower bound in thm:limit.
Use: derive all compact numerical-analysis constants from genuine C¹
regularity. The final theorem assumes only a positive C¹ density and actual
C¹ type-time state equations; error, stability and convergence constants are
conclusions. No derivative-bound or recovery certificate is required.
Source: C¹ maps on convex compact sets are Lipschitz (mathlib), compact
boundedness, and the proved actual split-step consistency/Grönwall theorem.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set
open scoped BigOperators

/-- One common bound and Lipschitz constant follows from actual compact C¹
regularity of a scalar function. -/
theorem compact_C1_scalar_bounds {f : ℝ → ℝ} {Y : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc 0 Y)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y ∈ Icc 0 Y, |f y| ≤ C) ∧
      ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y, |f y - f z| ≤ C * |y - z| := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 Y) isCompact_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 0 M + K, by positivity, ?_, ?_⟩
  · intro y hy
    have ht := hM y hy
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (by have := le_max_right (0 : ℝ) M; have := K.property; linarith)
  · intro y hy z hz
    have ht := hK.dist_le_mul y hy z hz
    rw [Real.dist_eq, Real.dist_eq] at ht
    exact ht.trans (by gcongr; exact le_add_of_nonneg_left (le_max_left (0 : ℝ) M))

/-- Finitely many actual C¹ functions share genuine compact bounds. -/
theorem compact_C1_family_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → ℝ → ℝ} {Y : ℝ} (hF : ∀ i, ContDiffOn ℝ 1 (F i) (Icc 0 Y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      (∀ y ∈ Icc 0 Y, |F i y| ≤ C) ∧
      ∀ y ∈ Icc 0 Y, ∀ z ∈ Icc 0 Y, |F i y - F i z| ≤ C * |y - z| := by
  choose C hC hbound hLip using fun i ↦ compact_C1_scalar_bounds (hF i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ hC i), fun i ↦ ⟨?_, ?_⟩⟩
  · intro y hy
    exact (hbound i y hy).trans (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i))
  · intro y hy z hz
    exact (hLip i y hy z hz).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i)) (abs_nonneg _))

/-- Actual compact C¹ density/state data imply the printed uniform O(h)
state error for the genuine finite recovery strings. All constants and local
defects are proved internally, including the source midpoint/right samples. -/
theorem exists_recovery_state_error_bound {v φ p : ℝ → ℝ} {Y : ℝ} (hY : 0 < Y)
    (hv : ∀ y ∈ Icc 0 Y, 0 < v y)
    (hcv : ContDiffOn ℝ 1 v (Icc 0 Y))
    (hcφ : ContDiffOn ℝ 1 φ (Icc 0 Y)) (hcp : ContDiffOn ℝ 1 p (Icc 0 Y))
    (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1)
    (hφ : ∀ y ∈ Icc 0 Y, HasDerivWithinAt φ ((v y)⁻¹ * p y) (Icc 0 Y) y)
    (hp : ∀ y ∈ Icc 0 Y, HasDerivWithinAt p (v y * φ y) (Icc 0 Y) y) :
    ∃ C > (0 : ℝ), ∀ (h : ℝ) (hh : 0 < h), h ≤ 1 → ∀ N : ℕ, ∀ hNY : (N : ℝ) * h ≤ Y,
      ∀ j ≤ N, let S := recoveryString v hh N hNY hv
      ‖(S.φ j, S.p j) - (φ ((j : ℝ) * h), p ((j : ℝ) * h))‖ ≤ C * h := by
  have hci : ContDiffOn ℝ 1 (fun y ↦ (v y)⁻¹) (Icc 0 Y) := hcv.inv (fun y hy ↦ (hv y hy).ne')
  let F : Fin 6 → ℝ → ℝ := ![v, (fun y ↦ (v y)⁻¹), φ, p,
    (fun y ↦ (v y)⁻¹ * p y), (fun y ↦ v y * φ y)]
  have hF : ∀ i, ContDiffOn ℝ 1 (F i) (Icc 0 Y) := by
    intro i
    fin_cases i
    · exact hcv
    · exact hci
    · exact hcφ
    · exact hcp
    · exact hci.mul hcp
    · exact hcv.mul hcφ
  obtain ⟨K, hK, hall⟩ := compact_C1_family_bounds hF
  let C := ((K + K ^ 2) * K + K) * Y * exp ((K + K ^ 2) * Y)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by positivity, ?_⟩
  intro h hh hh₁ N hNY j hj
  have hbound := recovery_state_error_bound hh hh₁ hNY hK hK hK hK hv
    (fun y hy ↦ ⟨(hall 0).1 y hy, (hall 1).1 y hy⟩)
    (fun y hy ↦ ⟨(hall 2).1 y hy, (hall 3).1 y hy⟩)
    (fun y hy z hz ↦ ⟨(hall 0).2 y hy z hz, (hall 1).2 y hy z hz⟩)
    hφ₀ hp₀ hφ hp ((hall 4).2) ((hall 5).2) hj
  change ‖((recoveryString v hh N hNY hv).φ j, (recoveryString v hh N hNY hv).p j) -
    (φ ((j : ℝ) * h), p ((j : ℝ) * h))‖ ≤ _ at hbound ⊢
  exact hbound.trans (by dsimp [C]; nlinarith only [hh])

end
end krylov.Asymptotics

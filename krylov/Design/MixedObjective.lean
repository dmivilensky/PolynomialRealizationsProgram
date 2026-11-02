import krylov.Design.ChristoffelObjective
import Mathlib.Tactic.FunProp

/-!
Article: main_krylov, thm:B, existence for mixed extrapolation design.
Use: attain the true mixed objective on all probability measures of a compact
spectral interval, with arbitrary nonnegative weights and positive exponent.
Source: Pukelsheim93; mathlib compactness of probability measures replaces a
separate compactness proof. No moment invertibility or atomic optimizer is assumed.
-/

namespace krylov.Design
noncomputable section
open Set MeasureTheory
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The mixed Christoffel objective, including zero weights and singular measures.
Article: main_krylov, thm:B. -/
def mixedObjective (M : ℕ) (w : Fin M → ℝ) (γ a : ℝ) (x : C(X, ℝ))
    (ν : ProbabilityMeasure X) : ℝ :=
  ∑ i : Fin M, w i * (christoffel (i.val + 1) a x ν) ^ γ

/-- Every term and hence the mixed objective is nonnegative.
Article: main_krylov, thm:B. Proof: information, weights and real powers are nonnegative. -/
theorem mixedObjective_nonneg (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    (γ a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    0 ≤ mixedObjective M w γ a x ν := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i)
    (Real.rpow_nonneg (christoffel_nonneg _ _ _ _) _)

/-- The mixed criterion is bounded by the sum of its weights.
Article: main_krylov, thm:B. Proof: the constant polynomial bounds each information by one. -/
theorem mixedObjective_le_sum (M : ℕ) (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i)
    {γ : ℝ} (hγ : 0 ≤ γ) (a : ℝ) (x : C(X, ℝ)) (ν : ProbabilityMeasure X) :
    mixedObjective M w γ a x ν ≤ ∑ i, w i := by
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ w i * (1 : ℝ) ^ γ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (christoffel_nonneg _ _ _ _) (christoffel_le_one _ _ _ _) hγ) (hw i)
    _ = w i := by rw [Real.one_rpow, mul_one]

variable [CompactSpace X] [BorelSpace X]

/-- Positive powers of information are upper semicontinuous across rank loss.
Article: main_krylov, thm:B.
Proof: extend the real power monotonically using max(t,0), then compose semicontinuously. -/
theorem upperSemicontinuous_weighted_christoffel (m : ℕ) (a : ℝ) (x : C(X, ℝ))
    {w γ : ℝ} (hw : 0 ≤ w) (hγ : 0 ≤ γ) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure X => w * (christoffel m a x ν) ^ γ) := by
  have hc : Continuous (fun t : ℝ => w * (max t 0) ^ γ) :=
    continuous_const.mul ((Real.continuous_rpow_const hγ).comp (continuous_id.max continuous_const))
  have hm : Monotone (fun t : ℝ => w * (max t 0) ^ γ) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_max_right _ _) (max_le_max_right _ hst) hγ) hw
  simpa only [Function.comp_def, max_eq_left (christoffel_nonneg m a x _)] using
    hc.comp_upperSemicontinuous (upperSemicontinuous_christoffel m a x) hm

/-- A finite nonnegative mixture is upper semicontinuous on the full measure space.
Article: main_krylov, thm:B. Proof: induction on the finite sum of semicontinuous terms. -/
theorem upperSemicontinuous_mixedObjective (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ : 0 ≤ γ) (a : ℝ) (x : C(X, ℝ)) :
    UpperSemicontinuous (mixedObjective M w γ a x) := by
  have hsum (s : Finset (Fin M)) :
      UpperSemicontinuous (fun ν : ProbabilityMeasure X =>
        ∑ i ∈ s, w i * (christoffel (i.val + 1) a x ν) ^ γ) := by
    induction s using Finset.induction_on with
    | empty => simpa using continuous_const.upperSemicontinuous
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (upperSemicontinuous_weighted_christoffel (i.val + 1) a x (hw i) hγ).add ih
  exact hsum Finset.univ

/-- The actual mixed design problem has a maximizing probability measure.
Article: main_krylov, thm:B, attainment part, including gamma=1 and zero weights.
Proof: weak compactness of all probability measures on the compact spectral space
and upper semicontinuity of the variational objective; no optimizer fields are assumed. -/
theorem mixedObjective_attains [T2Space X] [Nonempty X] (M : ℕ) (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) {γ : ℝ} (hγ : 0 ≤ γ) (a : ℝ) (x : C(X, ℝ)) :
    ∃ ν : ProbabilityMeasure X, ∀ ν',
      mixedObjective M w γ a x ν' ≤ mixedObjective M w γ a x ν := by
  let ν₀ : ProbabilityMeasure X := ⟨Measure.dirac (Classical.choice ‹Nonempty X›), by infer_instance⟩
  obtain ⟨ν, _, hν⟩ := UpperSemicontinuousOn.exists_isMaxOn
    (f := mixedObjective M w γ a x)
    (s := (Set.univ : Set (ProbabilityMeasure X))) ⟨ν₀, Set.mem_univ _⟩ isCompact_univ
    ((upperSemicontinuous_mixedObjective M w hw hγ a x).upperSemicontinuousOn _)
  exact ⟨ν, fun ν' => hν (Set.mem_univ ν')⟩

end
end krylov.Design

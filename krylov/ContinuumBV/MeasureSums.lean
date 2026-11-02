import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
Article: main_krylov, apC:lem:fund, identification of Taylor sums with BV integrals.
Use: control actual vector-measure integrals by finite tagged sums. The error
is the coefficient oscillation times the total variation and is independent
of the partition size. The measure may be singular or atomic.
Source: mathlib's vector-measure integral, simple functions and norm estimate.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X E V G ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Piecewise constant coefficient of a finite tagged measure partition. -/
def partitionCoefficient (s : Finset ι) (A : ι → Set X) (a : ι → E) (x : X) : E :=
  ∑ i ∈ s, (A i).indicator (fun _ => a i) x

omit [MeasurableSpace X] [NormedSpace ℝ E] in
/-- A finite partition coefficient has exactly its tagged value on each cell. -/
theorem partitionCoefficient_eq [DecidableEq ι] {s : Finset ι} {A : ι → Set X}
    {a : ι → E} (hdisj : (s : Set ι).PairwiseDisjoint A) {i : ι} (hi : i ∈ s) {x : X} (hx : x ∈ A i) :
    partitionCoefficient s A a x = a i := by
  unfold partitionCoefficient
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j hj hji
    exact indicator_of_notMem (fun hxj => (Set.disjoint_left.1 (hdisj hj hi hji)) hxj hx) _
  · intro hnot
    exact False.elim (hnot hi)

/-- The vector integral of the step coefficient is the actual tagged sum. -/
theorem integral_partitionCoefficient {μ : VectorMeasure X V} [IsFiniteMeasure μ.variation]
    (B : E →L[ℝ] V →L[ℝ] G) (s : Finset ι) (A : ι → Set X) (a : ι → E)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ᵛ x, partitionCoefficient s A a x ∂[B; μ]) = ∑ i ∈ s, B (a i) (μ (A i)) := by
  unfold partitionCoefficient
  rw [VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact VectorMeasure.integral_indicator_const (μ := μ) (B := B) (a i) (hA i hi)
  · intro i hi
    exact (integrable_const (a i)).indicator (hA i hi)

/-- Uniform coefficient oscillation on each cell bounds the tagged-sum error
against the genuine vector-measure integral. No density is required. -/
theorem norm_tagged_sum_sub_integral_le [DecidableEq ι]
    {μ : VectorMeasure X V} [IsFiniteMeasure μ.variation]
    (B : E →L[ℝ] V →L[ℝ] G) (s : Finset ι) (A : ι → Set X) (a : ι → E)
    {c : X → E} {ε : ℝ}
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hdisj : (s : Set ι).PairwiseDisjoint A)
    (hcover : ∀ᵐ x ∂μ.variation, ∃ i ∈ s, x ∈ A i)
    (hc : μ.Integrable c) (hosc : ∀ i ∈ s, ∀ x ∈ A i, ‖a i - c x‖ ≤ ε) :
    ‖(∑ i ∈ s, B (a i) (μ (A i))) - (∫ᵛ x, c x ∂[B; μ])‖ ≤
      ε * ‖B‖ * μ.variation.real univ := by
  have hstep : μ.Integrable (partitionCoefficient s A a) := by
    apply VectorMeasure.Integrable.fun_finsetSum s
    intro i hi
    exact (integrable_const (a i)).indicator (hA i hi)
  rw [← integral_partitionCoefficient B s A a hA,
    ← VectorMeasure.integral_fun_sub hstep hc]
  apply VectorMeasure.norm_integral_le_of_norm_le_const
  filter_upwards [hcover] with x hx
  obtain ⟨i, hi, hxi⟩ := hx
  rw [partitionCoefficient_eq hdisj hi hxi]
  exact hosc i hi x hxi

end
end krylov.ContinuumBV

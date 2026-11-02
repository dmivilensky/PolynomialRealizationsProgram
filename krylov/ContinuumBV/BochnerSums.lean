import krylov.ContinuumBV.MeasureSums
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: main_krylov, apC:lem:fund, physical measure representation.
Use: compare the same finite tagged sums with ordinary Bochner integrals
of a continuously varying derivative applied to an integrable state density.
The error uses coefficient oscillation times the integral of the density norm.
Source: finite simple functions, continuous-linear-map integration and norm bounds.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory

variable {X V ι : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [MeasurableSpace X] [CompleteSpace V] in
/-- Evaluation of the piecewise constant operator is a genuine finite
simple partition applied to the physical density. -/
theorem partitionCoefficient_apply (s : Finset ι) (A : ι → Set X)
    (a : ι → V →L[ℝ] ℝ) (h : X → V) (x : X) :
    partitionCoefficient s A a x (h x) =
      ∑ i ∈ s, (A i).indicator (fun y => a i (h y)) x := by
  unfold partitionCoefficient
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hx : x ∈ A i <;> simp only [indicator, hx, ite_true, ite_false,
    zero_apply]

/-- Tagged state-density sums are exactly the integral of their true step
operator acting on the physical density. -/
theorem integral_partitionCoefficient_apply {μ : Measure X} {h : X → V}
    (hi : Integrable h μ) (s : Finset ι) (A : ι → Set X) (a : ι → V →L[ℝ] ℝ)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    (∫ x, partitionCoefficient s A a x (h x) ∂μ) = ∑ i ∈ s, a i (∫ x in A i, h x ∂μ) := by
  simp_rw [partitionCoefficient_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi'
    rw [integral_indicator (hA i hi')]
    exact (a i).integral_comp_comm (hi.integrableOn)
  · intro i hi'
    exact ((a i).integrable_comp hi).indicator (hA i hi')

/-- Uniform operator oscillation controls the physical Bochner integral by
the identical tagged sum used for the BV vector-measure integral. -/
theorem norm_density_tagged_sum_sub_integral_le [DecidableEq ι]
    {μ : Measure X} {h : X → V} (hi : Integrable h μ)
    (s : Finset ι) (A : ι → Set X) (a : ι → V →L[ℝ] ℝ)
    {c : X → V →L[ℝ] ℝ} {ε : ℝ}
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hdisj : (s : Set ι).PairwiseDisjoint A)
    (hcover : ∀ᵐ x ∂μ, ∃ i ∈ s, x ∈ A i)
    (hc : Integrable (fun x => c x (h x)) μ)
    (hosc : ∀ i ∈ s, ∀ x ∈ A i, ‖a i - c x‖ ≤ ε) :
    ‖(∑ i ∈ s, a i (∫ x in A i, h x ∂μ)) - (∫ x, c x (h x) ∂μ)‖ ≤
      ε * ∫ x, ‖h x‖ ∂μ := by
  have hstep : Integrable (fun x => partitionCoefficient s A a x (h x)) μ := by
    simp_rw [partitionCoefficient_apply]
    apply integrable_finsetSum s
    intro i hi'
    exact ((a i).integrable_comp hi).indicator (hA i hi')
  rw [← integral_partitionCoefficient_apply hi s A a hA, ← integral_sub hstep hc,
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hi.norm.const_mul ε)
  filter_upwards [hcover] with x hx
  obtain ⟨i, hi', hxi⟩ := hx
  rw [partitionCoefficient_eq hdisj hi' hxi]
  calc
    ‖a i (h x) - c x (h x)‖ = ‖(a i - c x) (h x)‖ := rfl
    _ ≤ ‖a i - c x‖ * ‖h x‖ := (a i - c x).le_opNorm _
    _ ≤ ε * ‖h x‖ := mul_le_mul_of_nonneg_right (hosc i hi' x hxi) (norm_nonneg _)

end
end krylov.ContinuumBV

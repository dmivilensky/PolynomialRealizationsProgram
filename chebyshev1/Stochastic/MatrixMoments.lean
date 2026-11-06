import chebyshev1.Stochastic.IndependentSpectral

/-! The matrix-entry L² hypotheses are exactly finite Hilbert--Schmidt second moment. -/
namespace chebyshev1.Stochastic
noncomputable section
open MeasureTheory
open scoped BigOperators
variable {d Ω : Type*} [Fintype d] [MeasurableSpace Ω] {μ : Measure Ω}

theorem matrix_entry_sq_le_hsSq (M : Matrix d d ℝ) (i j : d) :
    (M i j)^2 ≤ hsSq M := by
  calc
    _ ≤ ∑ k, (M i k)^2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ hsSq M := Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)

theorem matrix_entry_memLp_of_hsSq_integrable (M : Ω → Matrix d d ℝ)
    (hm : Measurable M) (hH : Integrable (fun ω => hsSq (M ω)) μ) (i j : d) :
    MemLp (fun ω => M ω i j) 2 μ := by
  apply (memLp_two_iff_integrable_sq hm.eval_matrix.aestronglyMeasurable).mpr
  apply hH.mono' (hm.eval_matrix.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    simpa only [Real.norm_eq_abs,abs_pow,sq_abs] using matrix_entry_sq_le_hsSq (M ω) i j)

theorem hsSq_integrable_of_matrix_entry_memLp (M : Ω → Matrix d d ℝ)
    (hL2 : ∀ i j, MemLp (fun ω => M ω i j) 2 μ) :
    Integrable (fun ω => hsSq (M ω)) μ := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hL2 i j).integrable_sq))

theorem matrix_entry_memLp_iff_hsSq_integrable (M : Ω → Matrix d d ℝ) (hm : Measurable M) :
    (∀ i j, MemLp (fun ω => M ω i j) 2 μ) ↔ Integrable (fun ω => hsSq (M ω)) μ :=
  ⟨hsSq_integrable_of_matrix_entry_memLp M,
    fun hH => matrix_entry_memLp_of_hsSq_integrable M hm hH⟩

end
end chebyshev1.Stochastic

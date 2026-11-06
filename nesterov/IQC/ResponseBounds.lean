import nesterov.IQC.Observation

/-! Uniform ℓ² estimates for the actual free and forced finite-memory responses. -/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC
variable {E : Type*} [NormedAddCommGroup E]

theorem prefixNorm_le_sum_norm (x : ℕ→E) (N : ℕ) :
    prefixNorm x N≤∑ n∈Finset.range N,‖x n‖ := by
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.range N) (f:=fun n=>‖x n‖)
    (fun _ _=>norm_nonneg _)
  rw [←prefixNorm_sq] at hh
  exact (sq_le_sq₀ (prefixNorm_nonneg _ _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).mp hh

/-- An ℓ¹ scalar majorant supplies both square summability and an ℓ² gain. -/
theorem squareSummable_of_norm_majorant {x : ℕ→E} {a : ℕ→ℝ} {C : ℝ}
    (ha : ∀ n,0≤a n) (hs : Summable a) (hC : 0≤C)
    (hx : ∀ n,‖x n‖≤a n*C) :
    SquareSummable x ∧ sequenceNorm x≤(∑' n,a n)*C := by
  have hp (N : ℕ) : prefixNorm x N≤(∑' n,a n)*C := by
    calc
      _≤∑ n∈Finset.range N,‖x n‖:=prefixNorm_le_sum_norm x N
      _≤∑ n∈Finset.range N,a n*C:=Finset.sum_le_sum (fun n _=>hx n)
      _=(∑ n∈Finset.range N,a n)*C:=by rw [Finset.sum_mul]
      _≤_:=mul_le_mul_of_nonneg_right
        (hs.sum_le_tsum (Finset.range N) (fun n _=>ha n)) hC
  exact ⟨squareSummable_of_prefix_bound hp,
    sequenceNorm_le_of_prefix_bound (mul_nonneg (tsum_nonneg ha) hC) hp⟩

theorem sequenceNorm_add_le {x y : ℕ→E} (hx : SquareSummable x) (hy : SquareSummable y) :
    sequenceNorm (x+y)≤sequenceNorm x+sequenceNorm y := by
  apply sequenceNorm_le_of_prefix_bound (add_nonneg (sequenceNorm_nonneg _) (sequenceNorm_nonneg _))
  intro N
  exact (prefixNorm_triangle x y N).trans
    (add_le_add (prefixNorm_le_sequenceNorm hx N) (prefixNorm_le_sequenceNorm hy N))

variable [NormedSpace ℝ E]
variable {d : ℕ}

theorem freeState_squareSummable_norm (a : Fin d→ℝ) (initial : Fin d→E)
    (hs : Summable (fun n : ℕ=>‖companion d (fun j=>(a j:ℂ))^n‖)) (i : Fin d) :
    SquareSummable (fun n=>freeState a initial n i) ∧
      sequenceNorm (fun n=>freeState a initial n i)≤
        (∑' n,‖companion d (fun j=>(a j:ℂ))^n‖)*(∑ j,‖initial j‖) :=
  squareSummable_of_norm_majorant (fun _=>norm_nonneg _) hs
    (Finset.sum_nonneg (fun _ _=>norm_nonneg _)) (fun n=>freeState_norm a initial n i)

theorem freeObservation_norm (a q : Fin d→ℝ) (initial : Fin d→E) (n : ℕ) :
    ‖freeObservation a q initial n‖≤
      ‖companion d (fun j=>(a j:ℂ))^n‖*((∑ i,|q i|)*(∑ j,‖initial j‖)) := by
  calc
    _≤∑ i,‖q i • freeState a initial n i‖:=norm_sum_le _ _
    _=∑ i,|q i| * ‖freeState a initial n i‖:=by simp only [norm_smul,Real.norm_eq_abs]
    _≤∑ i,|q i| * (‖companion d (fun j=>(a j:ℂ))^n‖*(∑ j,‖initial j‖)):=by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (freeState_norm a initial n i) (abs_nonneg _)
    _=_:=by rw [←Finset.sum_mul]; ring

theorem freeObservation_squareSummable_norm (a q : Fin d→ℝ) (initial : Fin d→E)
    (hs : Summable (fun n : ℕ=>‖companion d (fun j=>(a j:ℂ))^n‖)) :
    SquareSummable (freeObservation a q initial) ∧
      sequenceNorm (freeObservation a q initial)≤
        (∑' n,‖companion d (fun j=>(a j:ℂ))^n‖)*((∑ i,|q i|)*(∑ j,‖initial j‖)) :=
  squareSummable_of_norm_majorant (fun _=>norm_nonneg _) hs
    (mul_nonneg (Finset.sum_nonneg (fun _ _=>abs_nonneg _))
      (Finset.sum_nonneg (fun _ _=>norm_nonneg _))) (fun n=>freeObservation_norm a q initial n)

end
end nesterov.IQC

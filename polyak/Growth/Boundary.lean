import polyak.Growth.Discount
import polyak.Growth.Extension

/-!
Article: Appendix A, Lemma plateau, bounded initial windows.
Use: one constant controls every run and every dimension; shifts preserve discounting exactly.
Proof: apply Γ to each finite prefix, then sum finitely many nonnegative terms.
-/

namespace polyak.Growth
noncomputable section
open Finset

/-- Article: the initial-window bound. Use: a finite constant independent of trajectory and dimension. -/
def boundaryConstant (A B β t : ℝ) (m : ℕ) : ℝ :=
  1+∑ k ∈ Ico 0 m, Real.exp (-2*k*t)*envelope A B β k^2

/-- Article: the initial-window bound. Use: a strictly positive constant including empty windows. -/
theorem boundaryConstant_pos (A B β t : ℝ) (m : ℕ) : 0 < boundaryConstant A B β t m := by
  have hh : 0 ≤ ∑ k ∈ Ico 0 m, Real.exp (-2*k*t)*envelope A B β k^2 := by
    exact sum_nonneg (fun _ _ => by positivity)
  dsimp [boundaryConstant]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A B β : ℝ}

/-- Article: a free trajectory obeys Γ on every prefix. Use: actual runs enter the exact envelope. -/
theorem Run.norm_le_envelope (r : Run E A B β) (k : ℕ) :
    ‖r.x k‖ ≤ envelope A B β k * stateNorm r.x 0 := by
  exact (norm_left_le_stateNorm r.x k).trans (stateNorm_le_envelope_hilbert (r.segment k))

/-- Article: initial-window estimate. Use: bound the finite window uniformly before the plateau argument. -/
theorem Run.mass_le_boundaryConstant (r : Run E A B β) (t : ℝ) (m : ℕ) :
    mass (discountedEnergy r.x t) 0 m ≤
      boundaryConstant A B β t m * stateNorm r.x 0^2 := by
  calc
    _ ≤ ∑ k ∈ Ico 0 m, (Real.exp (-2*k*t)*envelope A B β k^2)*stateNorm r.x 0^2 := by
      apply sum_le_sum
      intro k _
      have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (envelope_nonneg A B β k)
        (stateNorm_nonneg r.x 0))).mpr (r.norm_le_envelope k)
      have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*k*t)).le
      simpa only [discountedEnergy, mul_pow, mul_assoc] using hw
    _ = (∑ k ∈ Ico 0 m, Real.exp (-2*k*t)*envelope A B β k^2)*stateNorm r.x 0^2 :=
      (sum_mul _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [boundaryConstant]
      linarith

/-- Article: shifted free trajectory. Use: apply one uniform estimate to any tail. -/
def Run.shift (r : Run E A B β) (i : ℕ) : Run E A B β where
  ψ := r.ψ
  normalized := r.normalized
  x k := r.x (i+k)
  recurrence k := by simpa only [Nat.add_assoc] using r.recurrence (i+k)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Article: exact shift of the discounted energy. Use: no constants are lost by translating a window. -/
theorem discountedEnergy_shift (x : ℕ → E) (t : ℝ) (i k : ℕ) :
    discountedEnergy (fun k => x (i+k)) t k =
      Real.exp (2*i*t)*discountedEnergy x t (i+k) := by
  unfold discountedEnergy
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

end
end polyak.Growth
